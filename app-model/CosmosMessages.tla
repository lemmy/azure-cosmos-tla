---- MODULE CosmosMessages ----
EXTENDS Integers

Hierarchy ==
    \* This is more of partial order than total order because of session consistency.
    [
        Strong |-> 5, Bounded_staleness |-> 4, Session |-> 3, Consistent_prefix |-> 2, Eventual |-> 1
    ]

Levels ==
    \*{"Strong", "Bounded_staleness", "Session", "Consistent_prefix", "Eventual"}
    DOMAIN Hierarchy

Consistency ==
    [level: Levels, lsn: Int] \* log-sequence-number (lsn)

CONSTANT Regions

CONSTANT Clients

CONSTANT Null, Data

\* Request: Client -> Cosmos
Request ==
    [
        doc: STRING,     \* The document that was read.
        \* data: Data,      \* The data that was read.
        type: {"Read"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: Clients    \* The client that originally sent the read request.
    ] \cup
    [
        doc: STRING,     \* The document that was written.
        data: Data,      \* The data that was written.
        old: Data \cup {Null},    \* If not Null, the expected data to be overriden (If-Match).  Note that If-Match & etags are essentially compare-and-swap.
        type: {"Write"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original write request was sent to.
        orig: Clients
    ]

\* Response: Cosmos -> Client
Response ==
    [
        doc: STRING,     \* The document that was written.
        data: Data,    \* "ACK", a session token, or the data that was read.
        type: {"Reply", "Error"}, 
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ] \cup 
    [
        doc: STRING,       \* The document that was written.
        \* Cosmos' write response contains the original data: 
        \* https://docs.microsoft.com/en-us/rest/api/cosmos-db/create-a-document#example
        data: Data \cup {Null},      \* Null if Error.
        \* In case of error, the write might or might not have succeeded. An error
        \* models the case that the database response to a write request was lost.
        \* Message duplications is assumed to be prevented by the communicaion
        \* protocol (e.g. TCP).
        type: {"ACK", "NACK", "Error"},
        consistency: Consistency, 
        region: Regions, \* The region the original read request was sent to.
        orig: {"cosmos"}
    ]

CRead(doc, consistency, region, orig) ==
    [
        doc |-> doc, 
        type |-> "Read", consistency |-> consistency,
        region |-> region, orig |-> orig
    ]

CRequest(doc, data, old, type, consistency, region, orig) ==
    [
        doc |-> doc, data |-> data, old |-> old,
        type |-> type, consistency |-> consistency,
        region |-> region, orig |-> orig
    ]

CError(request) ==
    [
        doc |-> request.doc, data |-> Null,
        type |-> "Error", consistency |-> [level |-> request.consistency.level, lsn |-> -1],
        region |-> request.region, orig |-> "cosmos"
    ]

CReply(request, data, lsn) ==
    [
        doc |-> request.doc, data |-> data,
        type |-> "Reply", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]

CAck(request, data, lsn) ==
    [
        doc |-> request.doc, data |-> data,
        type |-> "ACK", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]

CNack(request, data, lsn) ==
    [
        doc |-> request.doc, data |-> data,
        type |-> "NACK", consistency |-> [level |-> request.consistency.level, lsn |-> lsn],
        region |-> request.region, orig |-> "cosmos"
    ]
======