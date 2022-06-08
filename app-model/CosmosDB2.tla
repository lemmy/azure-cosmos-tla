### Supported:
- All five consistency levels
- Downgrading consistency levels on a per-request basis for reads
- Optimistic Concurrency Control (OCC), i.e., if-match (simplified to CAS)

- Multi-region accounts/Write-region failover!
https://docs.microsoft.com/en-us/azure/cosmos-db/high-availability#replica-outages

### Out of scope/Unsupported:
- Multi-region writes
- Disaster recovery/backups
- Conflict resolution
- Change feed
- Range queries across partition keys
- Stored procedures/triggers/UDFs
- Any kind of query language
- ...anything not mentiond above!

------ MODULE CosmosDB2 -----
EXTENDS Functions, Sequences, FiniteSets

E ==
    \* If true, reads and writes exhibit errors.
    TRUE

CONSTANT Regions

CONSTANT Null, Data

CONSTANT Clients

INSTANCE CosmosMessages

VARIABLE
    \* The log variable models Cosmos DB, such that it contains the sequence of (read & write)
    \* requests (operations) that have been executed against the database. Note that there is
    \* no need to replicate the log across replicas or regions, because both concepts are left
    \* implicit in this spec; it is up to the read and write actions below to model the various
    \* anomoaies that can occur. In other words, log is a sequence of requests, which is
    \* essentially a global Write-Ahead log.
    \** Since we don't care about an efficient implementation of Cosmos DB, we never
    \** checkpoint/apply and discard a prefix of the WAL. Discarding the WAL, however, could be
    \** an optimization to speed-up model-checking by applying a prefix of the WAL into a "db entry".
    log,
    \* The writeRegion is the currently select region that accepts write requests from clients.
    \* The writeRegion may fail over to a different region, forcing clients to send write requests
    \* to the new writeRegion.  If Cosmos runs under a consistency level other than Strong, a
    \* failover of the writeRegion can cause data loss.
    writeRegion

--------------------------------------------------------------------------------

Writes ==
    { req \in log: req.type = "Write" }

Reads ==
    { req \in log: req.type = "Read" }

DefaultConsistencyLevel ==
    \* The databases's default consistency level.
    \** Consider turning this a spec constant to speed up model-checking. 
    CHOOSE cl \in { w.consistency.level : w \in Writes }: TRUE

--------------------------------------------------------------------------------

CTypeOK ==
    /\ log \in Seq(Request)
    \* The write consistency level cannot be changed on a per-request basis.
    /\ Cardinality(DefaultConsistencyLevel) = 1
    \* The read consistency level can be changed on a per-request basis to any
    \* consistency level less than or equal to Cosmos' default (write) consistency
    \* level.
    /\ \A r \in Reads: Hierarchy[r.consistency.level] <= Hierarchy[DefaultConsistencyLevel]
    \* The write region is selected among all regions.
    /\ writeRegion \in Regions

--------------------------------------------------------------------------------

LastLSN(doc) ==
    CHOOSE i \in 1..Len(log):
            /\ log[i].type = "Write"
            /\ log[i].doc = doc
            /\ \A j \in (i+1)..Len(log): \/ log[j].type # "Write"
                                         \/ log[j].doc # doc

LastData(doc) ==
    \* Null or the data of the last write.
    IF \E w \in Range(log): w.type = "Write" /\ w.doc = doc
    THEN log[LastLSN(doc)].data
    ELSE Null

--------------------------------------------------------------------------------

\* 
ReadStrong(request) ==
    IF \E w \in Range(log): w.type = "Write" /\ w.doc = request.doc
    THEN {CReply(request, LastData(request.doc), LastLSN(request.doc))}
    ELSE {} \* 404 in Cosmos DB

ReadBounded(request) ==
    FALSE \* TODO

\* A read under session consistency is carried out against a single replica.  The read
\* will block until the replica has been updated to the LSN greater than or equal to the
\* session token.
\* ??? - Under session consistency, a read without session token degrades to consistent prefix?
\* ??? - Does a read under session consistency return the newest session token or just the data?
ReadSession(request) ==
    \* If WritesrInRange = {}, no value for that doc has ever been written.
    \* This is a 404 in Cosmos DB, which we model as {} here.
    LET InRange == { log[i] : i \in request.consistency.lsn..Len(log) }
        WritesInRange == { w \in InRange : w.type = "Write" /\ w.doc = request.doc }
    IN { CReply(request, w.data, w.consistency.lsn) : w \in WritesInRange }
    \* TODO: We don't explicitly model the database's consistency level.  Instead, we
    \* TODO: expect the clients to include the desired consistency level in each requests.
    \* TODO: To model a read without a session token while the database operates under
    \* TODO: session consistency, the client has to set the requets's consistency level to
    \* TODO: "Consistet_prefix".

\* ??? - Does consistent prefix hold across reads to different regions? E.g. will a read in region B,
\* ???   that follows a read in region A that returned LSN 2, be guaranteed to return LSN >= 2?
ReadConsistentPrefix(request) ==
    \* TODO: Under consisten prefix, we may read any write older than the last read
    \* TODO: of that client in that region. If this is the first read by that client,
    \* TODO: non-deterministically return any write, and 404.
    FALSE 

\* Under eventual consistency, we may read any write (of that doc). Because a read under
\* eventual consistency is serviced by a single replica, even a subsequent read in the
\* same region can return older data.
ReadEventual(request) ==
    \* TODO: Non-deterministically return any write (matching the doc) and 404 (to model
    \* TODO: the case that the doc has never been written or not yet replicated). 
    FALSE

\*For strong and bounded staleness, reads are done against two replicas in a four replica set (minority quorum) to provide consistency guarantees.
\* Strong ->            Local Minority
\* Bounded Staleness -> Local Minority
\* Session ->           Single Replica (using session token)
\* Consistent Prefix -> Single Replica
\* Eventual ->          Single Replica
\* (see https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#consistency-levels-and-throughput)
ReadResponse(request) ==
    (IF E THEN {CError(request)} ELSE {}) \cup
    CASE request.consistency.level = "Strong" -> ReadStrong(request)
        [] request.consistency.level = "Bounded_staleness" -> ReadBounded(request)
        [] request.consistency.level = "Session" -> ReadSession(request)
        [] request.consistency.level = "Consistent_prefix" -> ReadConsistentPrefix(request)
        [] request.consistency.level = "Eventual" -> ReadEventual(request)

CosmosRead ==
    \E req \in {}: \* TODO: Model inbox
        /\ req.type = "Read"
        /\ log' = Append(log, req)
        /\ \E res \in ReadResponse(req):
            TRUE \* TODO: Model outbox 

--------------------------------------------------------------------------------

Write(request) ==
    IF \/ request.old = Null
       \* Optimistic concurrency control (OCC)
       \* Modeling if-match by comparing data values gives us CAS.  We could explicitly model _etags or reuse
       \* the doc's LSN to model LL/SC to prevent the ABA problem (https://en.wikipedia.org/wiki/ABA_problem).
       \/ request.old = LastData(request.doc)
    \* Can't use LastData' and Len(log') here bc log' not yet
    \* defined when TLC evaluates this expr. :-(
    THEN {CAck(request, request.data, Len(log') + 1)}
    ELSE {CNack(request, LastData(request.doc), Len(log))}

\* Strong ->            Global Majority
\* Bounded Staleness -> Local Majority
\* Session ->           Local Majority
\* Consistent Prefix -> Local Majority
\* Eventual ->          Local Majority
\* (see https://docs.microsoft.com/en-us/azure/cosmos-db/consistency-levels#consistency-levels-and-throughput)
\*
\* Writes always go to a (global or local) majority of replicas. Given that we do *not* model multi-region writes,
\* or individual replicas of a replica set, the spec can ignore the consistency levels during writes. The case
\* where the write region fails is subsumed by (non-deterministically) responding with CError.
WriteResponse(request) ==
    (IF E THEN {CError(request)} ELSE {}) \cup Write(request)

CosmosWrite ==
    \E req \in {}: \* TODO: Model inbox
        /\ req.type = "Write"
        /\ \E res \in WriteResponse(req):
            \* In case of an Error response, the write succeed or fails non-deterministically (hence Error appears
            \* in both disjuncts).
            \/ /\ res.type \in {"ACK", "Error"}
               /\ log' = Append(log, req)
            \/ /\ res.type \in {"NACK", "Error"}
               /\ UNCHANGED log
        /\ TRUE \* TODO: Model outbox 

\* Assume Default Consistency Level # "Strong":
\* Suppose we model a write region outage by non-deterministically removing the "unobserved" writes from the
\* log, i.e., we drop the suffix of writes in logs that follow all read operations in other region (a read
\* in the write operation itself doesn't imply that the writes were replicated):  
\* ??? Can this cause the LSN to go backwards?
\* ??? What happens if a client fails over to the new write regions but uses a session token of old region?
CosmosFailover ==
    /\ \E req \in log:
            \* There is no need to model failover under strong consistency, because a failover of the write region
            \* under strong consistency does not induce data loss; the clients transparently fail over to a new write
            \* region (causing latency to  change, which is not a concern of this model).
            \/ req.consistency.level \in {"Session", "Consistent_prefix", "Eventual"}
            \* Bounded staleness with a single region effectively provides strong consistency. With more than one region,
            \* strong consistency doesn't hold as outlined in https://github.com/MicrosoftDocs/azure-docs/issues/92341#issue-1223519438)
            \/ /\ req.consistency.level = "Bounded_staleness"
               /\ Cardinality({r.region : r \in log}) > 1
    \* 
    /\ LET UnobservedRequests == CHOOSE i \in 1..Len(log) : \A j \in i..Len(log): log[j].region 
       IN \* ??? Do we have to consider reads?
          \* A request has been observed operations/writes
          \* Non-deterministically drop all suffixes of the log that contain unobserved requests.  An unobserved
          \* write request is one whose effect has not been observed (read) in another region.
          /\ log' \in {}

================================================================================

## LSN (Log Sequence Number)
- The TLA+ spec model LSN's as a single, monotonically increasing counter (whereas Cosmos internally relies on Paxos to build a global sequencer).

## Transactions/Optimistic Concurrency Control
- For transactions, we need to model etags because if-match only supports matching on a doc's etag and not on arbitrary data values. Can potentially abstract into the LSN here.

## Consistency Levels

### Per-request consistency levels

#### Reads
Reads under a "weaker"^1 consistency level than the default one:
    - BS under Strong: Indistinguishable from a read under strong because the read is also served from a local minority.
    - SS under Strong: Let t be the session token. writes \in t..LastData(log) because read goes to a single replica but response will be blocked until replica has replicated writes to and including write corresponding to t.
    - CP under Strong: 
    - EV under Strong: Can observe any read in 1..LastData(log) because read can be served by any replica in any state.

    - SS under BS (not staleness window): t..LastData(log)
    - SS under BS (in staleness window):
    - CP under BS (not staleness window):
    - CP under BS (in staleness window):
    - EV under BS (not staleness window): 1..LastData(log)
    - EV under BS (in staleness window):  1..LastData(log)
 
    - CP under SS:
    - EV under SS:

    - EV under CP:

^1 "Weaker" consistency levels is ambiguous because there is no total order! There are reads that are served by a majority or by an arbitrary replica (that might be in any state). This is confirmed by the dotnet and Java SDKs, which do *not* distinguish between SS, CP, and EV except that the token is include under SS. Thus, the replica will not serve writes "staler" than t.
- https://github.com/Azure/azure-cosmos-dotnet-v3/blob/924c2e71baf35895b0b9a7f64c19315067436df2/Microsoft.Azure.Cosmos/src/ValidationHelpers.cs#L78-L107
- https://github.com/Azure/azure-cosmosdb-java/blob/e636aa509675ea059b1c565909d8f17d8641057d/commons/src/main/java/com/microsoft/azure/cosmosdb/internal/Utils.java#L374-L400

#### Writes
Writes cannot weaken the database's consistency level: https://docs.microsoft.com/en-in/azure/cosmos-db/sql/how-to-manage-consistency?tabs=portal%2Cdotnetv2%2Capi-async#override-the-default-consistency-level


## Log truncation to rule them all

Josh Rowe argues we don't need to model multiple regions iff
- we model a special operation that subsumes a read from the majority of regions (from which a client can learn that a write is durable)
- we subsume under a generic error a session token becoming invalid because of failover to another region

- Are anomalies due to relaxed consistency levels all faithfully represented by modeling log truncation (data loss)?
  * With bounded staleness, assuming a single write region, a read in the write region is equivalent to a read under strong consistency because a write under bounded staleness goes to the local majority of the write region and the read is served from the local majority.
  * => Thus, without modeling regions, a read under bound staleness must not exhibit a read anomaly when reading and writing to the write region.  However, the write region might fail over after the client's write.
  * => This scenario can be handled by inverting the problem:  If there is only one region (number of regions would be a constant) or there is no "service-managed" failover, we don't truncate the log! With more than one region, there are no strong consistency guarantees for reads and writes.



## Consistent Prefix, Eventual Consistency, and Session Consistency and Single Replica Reads

### Consistent Prefix

Under Consistent Prefix (CP), a read is served by a (single) replica, and a write has to be acknowledged by a *local* majority of replicas.  CP is implemented as a server-side consistency level, s.t., the replicas apply all writes in an order defined by the primary (more technically, replicas apply the replication messages in LSN-order) [1].  With a single region or a single write region and *no* failover (no availability on partitions), it is easy to see that clients will only observe gapless prefixes of all writes.

Assuming a durable write w1, suppose the following sequence of operations:

0) Client c1 reads w1
1) Client c1 writes w2 in region r1
2) Client c1 reads w2 in region r1
3) (Write) region r1 fails over to region r2 before write w2 has been replicated to r2.
4) Client c1 reads w1 in region r2

Client c1 read the following writes:
w1, w2, w1
    
Note that we ignore multi-master writes because multi-master has "orthogonal" consistency guarantees.

^1 This claim is support by a TLA+ spec [1] by Murat Demirbas (2018/19 visiting professor in CosmosDB), and a more detailed, internal specification [2 (neither of which model write region failover)].  Also, Consistent Prefix appears to be a late addition to Cosmos' consistency story, given that Cosmos's internal documentation rarely mentions it [3a,3b].  Note that a PR [4] that aims to model CP in the public Cosmos specs is incorrect and should be rejected; it models CP as a client-side enforced consistenty model.

### Consistent Prefix & Eventual Consistenc vs. Session Consistency

The same argument applies to Eventual Consistency with a strict interpretation that any (acknowledged) write is eventually observed.  Out of EV, CP, and SS (all reading from a single replica), only SS provides its promises if an account has multiple regions and failover.  Clients will receive an error if they read with an invalid session token due to a region failover.


[1] http://muratbuffalo.blogspot.com/2018/08/tla-specification-of-consistent-prefix.html
[2] https://msdata.visualstudio.com/CosmosDB/_git/CosmosDB?path=/Product/Tools/TLA/Specifications/ConsistencyModel/ConsistentPrefix.tla
[3a] https://msdata.visualstudio.com/CosmosDB/_git/CosmosDB?path=/Product/Microsoft.Azure.Documents/SharedFiles/ConsistencyReader.cs&version=GBmaster&line=16&lineEnd=17&lineStartColumn=1&lineEndColumn=1&lineStyle=plain&_a=contents
[3b] https://github.com/Azure/azure-cosmosdb-java/blob/e636aa509675ea059b1c565909d8f17d8641057d/direct-impl/src/main/java/com/microsoft/azure/cosmosdb/internal/directconnectivity/ConsistencyReader.java#L48-L158
[4] https://github.com/Azure/azure-cosmos-tla/pull/4


## MAKU Questions:

Is it feasible that CosmosDB was originally envisioned as a single write region database with *no* failover to read regions? With this configuration, the five consistency models work perfectly.  Clients only start exhibiting problems with more than one region *and* failover.  The fact that Strong Consistency shows no problems might be due to its definition, and -in light of multipe regions- just "accidentially" correct.  The various consistency specs model multiple regions (partitions), but they do *not* model failover.  Comments such as "Leader partition is elected statically through external consensus." further suggest it.