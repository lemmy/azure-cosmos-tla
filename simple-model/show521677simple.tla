---- MODULE show521677simple ----
EXTENDS TLC, Naturals, Sequences, IOUtils

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
 CONSTANTS VersionBound, StalenessBound

 
VARIABLES
    \* message queue
    queue, 
    
    \* database
    log,
    
    \* frontend
    requests, future,
    
    \* backend
    backend

specVars == <<queue, future, backend, requests>>

WriteConstLevel ==
    IF "WCL" \notin DOMAIN IOEnv THEN StrongConsistency
    ELSE
        CASE IOEnv.WCL = "strong" -> StrongConsistency
        []   IOEnv.WCL = "session" -> SessionConsistency
        []   IOEnv.WCL = "eventual" -> EventualConsistency
     
 VARIABLES commitIndex, readIndex, epoch

 Keys == {"k1", "k2"}
 Values == {"v1", "v2"}
 NoValue == "NoValue"

 dbVarsLog == <<commitIndex, readIndex, epoch>>
 dbVars == <<dbVarsLog, log>>
 vars == <<dbVars, specVars>>

 DB == INSTANCE CosmosDB WITH
            WriteConsistencyLevel <- WriteConstLevel,
            \* Don't model data loss. It is not needed, and it allows a session
            \* token to expire after being acquired. Handling that would
            \* complicate this spec.
            epoch <- epoch
 
 DBRead(t, k) ==
    IF "RCL" \notin DOMAIN IOEnv THEN DB!SessionConsistencyRead(t, k)
    ELSE
        CASE IOEnv.RCL = "strong" -> DB!StrongConsistencyRead(k)
        []   IOEnv.RCL = "session" -> DB!SessionConsistencyRead(t, k)
        []   IOEnv.RCL = "eventual" -> DB!EventualConsistencyRead(k)

 Nil == DB!NoSessionToken

 TypesOK == DB!TypesOK

---------------------------------------------------------------------

Init ==
    /\ queue = <<>>
    /\ future = Nil
    /\ backend = {}
    /\ requests = {[key |-> "k1", val |-> "v1"], [key |-> "k2", val |-> "v2"]}
    /\ DB!Init

1FrontendWrite ==
    \* Precondition: No pending write
    /\ future = Nil

    \* Write request to database
    /\ \E r \in requests:                                             
            DB!WriteInit(r.key, r.val, LAMBDA t: future' = t)

    \* Nothing else happens.
    /\ UNCHANGED <<dbVarsLog, requests, queue, backend>>

3FrontendEnqueue ==
    \* Precondition: Pending write that succeeded
    /\ future # Nil /\ DB!WriteSucceed(future)

    \* Acknowledge write to user
    /\ requests' =
        requests \ { [key |-> future.key, val |-> future.value ]}

    \* Enqueue write to backend
    /\ queue' = Append(queue, [ k |-> future.key, t |-> future ])

    \* Clear pending write
    /\ future' = Nil

    \* Nothing else happens.
    /\ UNCHANGED <<dbVars, backend>>

5BackendRead ==
    \* Precondition: Queue contains a msg
    /\ queue # <<>>

    \* Receive msg from queue
    /\ LET msg == Head(queue) IN
        \* Read from database (with the given key)                                 
        \E read \in DB!EventualConsistencyRead(msg.k) :
        \* \E read \in DB!SessionConsistencyRead(msg.t, msg.k) :
            backend' = backend \cup {read.value}

    \* Remove msg from queue
    /\ queue' = Tail(queue)                                           
    
    /\ UNCHANGED <<dbVars, requests, future>>

cosmos ==
    /\ DB!Next
    /\ UNCHANGED specVars

Next ==
    \/ 1FrontendWrite
    \/ 3FrontendEnqueue
    \/ 5BackendRead
    \/ cosmos

Spec == 
    Init /\ [][Next]_vars
        /\ WF_vars(1FrontendWrite) 
        /\ WF_vars(3FrontendEnqueue) 
        /\ WF_vars(5BackendRead)
        /\ WF_vars(UNCHANGED specVars /\ DB!IncreaseReadIndexAndOrCommitIndex)

----------------------------------------------------------------------------

BackendReceivesCorrectValue ==
    \A val \in Values:
        \* All acknowledged writes are eventually read by the backend.
        (val \notin { r.val : r \in requests } ~> val \in backend)

UniqueOrders ==
    \A i,j \in 1..Len(log):
        \* log is injective WRT keys
        log[i].key = log[j].key => i = j

AllProcessed ==
    <>[](requests = {})

Never404 ==
    NoValue \notin backend
----------------------------------------------------------------------------

Alias ==
    [
        log |-> log,
        queue |-> queue,
        future |-> future,
        backend |-> backend,
        requests |-> requests
    ]
====
