---- MODULE spec ----
EXTENDS Naturals, Sequences

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency, VersionBound, StalenessBound
 
VARIABLES
    \* database
    log,
    
    \* frontend
    requests, future,
    
    \* backend
    backend,

    \* message queue
    queue
    
specVars == <<queue, future, backend, requests>>

 VARIABLES commitIndex, readIndex, epoch

 Keys == {"o1", "o2"}
 Values == {"Yummy Pierogi", "Moar Pierogi"}
 NoValue == "NoValue"

 dbVarsLog == <<commitIndex, readIndex, epoch>>
 dbVars == <<dbVarsLog, log>>
 vars == <<dbVars, specVars>>

 DB == INSTANCE CosmosDB WITH epoch <- epoch,
            WriteConsistencyLevel <- StrongConsistency            

 Nil == DB!NoSessionToken

 TypesOK == DB!TypesOK

 Alias ==
    [ log |-> log, queue |-> queue, future |-> future, backend |-> backend, requests |-> requests ]

---------------------------------------------------------------------

Init ==
    /\ queue = <<>>
    /\ future = Nil
    /\ backend = {}
    /\ requests = {[key |-> "o1", val |-> "Yummy Pierogi"], 
                   [key |-> "o2", val |-> "Moar Pierogi"]}
    /\ DB!Init

12FrontendWrite ==
    \* Precondition: No pending write
    /\ future = Nil

    \* Write request to database
    /\ \E r \in requests: DB!WriteInit(r.key, r.val, LAMBDA t: future' = t)

    \* Nothing else happens.
    /\ UNCHANGED <<dbVarsLog, requests, queue, backend>>

34FrontendEnqueue ==
    \* Precondition: Pending write that succeeded
    /\ future # Nil /\ DB!WriteSucceed(future)

    \* Acknowledge write to user
    /\ requests' = requests \ { [key |-> future.key, val |-> future.value ]}

    \* Enqueue write to backend
    /\ queue' = Append(queue, [ k |-> future.key, t |-> Nil ])

    \* Clear pending write
    /\ future' = Nil

    \* Nothing else happens.
    /\ UNCHANGED <<dbVars, backend>>

56BackendRead ==
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

database ==
    /\ DB!Next
    /\ UNCHANGED specVars

Next ==
    \/ 12FrontendWrite
    \/ 34FrontendEnqueue
    \/ 56BackendRead
    \/ database

Spec == 
    Init /\ [][Next]_vars
        /\ WF_vars(12FrontendWrite) 
        /\ WF_vars(34FrontendEnqueue) 
        /\ WF_vars(56BackendRead)
        /\ WF_vars(UNCHANGED specVars /\ DB!IncreaseReadIndexAndOrCommitIndex)

----------------------------------------------------------------------------

BackendReceivesCorrectValue ==
    \A val \in Values:
        \* All acknowledged writes are eventually read by the backend.
        (val \notin { r.val : r \in requests } ~> val \in backend)

=============================================================================