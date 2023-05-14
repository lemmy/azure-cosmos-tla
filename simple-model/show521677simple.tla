---- MODULE show521677simple ----
EXTENDS TLC, Naturals, Sequences, IOUtils

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
 CONSTANTS VersionBound, StalenessBound

 WriteConstLevel ==
    IF "WCL" \notin DOMAIN IOEnv THEN StrongConsistency
    ELSE
        CASE IOEnv.WCL = "strong" -> StrongConsistency
        []   IOEnv.WCL = "session" -> SessionConsistency
        []   IOEnv.WCL = "eventual" -> EventualConsistency
     
 VARIABLES log, commitIndex, readIndex

 Keys == {"k"}
 Values == {"v1","v2"}
 NoValue == "NoValue"

 dbVarsLog == <<commitIndex, readIndex>>
 dbVars == <<dbVarsLog, log>>

 DB == INSTANCE CosmosDB WITH
            WriteConsistencyLevel <- WriteConstLevel,
            \* Don't model data loss. It is not needed, and it allows a session
            \* token to expire after being acquired. Handling that would
            \* complicate this spec.
            epoch <- 1
 
 DBRead(t, k) ==
    IF "RCL" \notin DOMAIN IOEnv THEN DB!StrongConsistencyRead(k)
    ELSE
        CASE IOEnv.RCL = "strong" -> DB!StrongConsistencyRead(k)
        []   IOEnv.RCL = "session" -> DB!SessionConsistencyRead(t, k)
        []   IOEnv.RCL = "eventual" -> DB!EventualConsistencyRead(k)

---------------------------------------------------------------------

Nil == DB!NoSessionToken

TypesOK == DB!TypesOK

VARIABLE queue, future, backend, requests

specVars == <<queue, future, backend, requests>>
vars == <<dbVars, specVars>>

Init ==
    /\ queue = <<>>
    /\ future = Nil
    /\ backend = NoValue
    /\ requests = Values
    /\ DB!Init

1FrontendWrite ==
    /\ future = Nil
    /\ \E val \in requests:
            DB!WriteInit("k", val, LAMBDA t: future' = t)
    /\ UNCHANGED <<dbVarsLog, requests, queue, backend>>

3FrontendEnqueue ==
    /\ future # Nil
    /\ DB!WriteSucceed(future)
    /\ requests' = requests \ { future.value }
    /\ queue' = << [ k |-> "k", t |-> future ] >>
    /\ UNCHANGED <<dbVars, future, backend>>

5BackendRead ==
    /\ queue # <<>>
    /\ LET msg == Head(queue) IN
       \E read \in DBRead(msg.t, msg.k) :
            backend' = read.value
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
    Init /\ [][Next]_vars /\ WF_vars(5BackendRead)

----------------------------------------------------------------------------

WorkerReceivesCorrectValue ==
    \A val \in Values:
        val \notin requests ~> backend = val

====
