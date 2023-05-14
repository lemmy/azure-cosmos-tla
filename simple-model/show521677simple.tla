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
        []  IOEnv.WCL = "session" -> SessionConsistency
        []  IOEnv.WCL = "eventual" -> EventualConsistency
     
 VARIABLES log, commitIndex, readIndex

 Keys == {"k"}
 Values == {"v1","v2"}
 NoValue == "NoValue"

 dbVarsExceptLog == <<commitIndex, readIndex>>
 dbVars == <<dbVarsExceptLog, log>>

 DB == INSTANCE CosmosDB WITH
            WriteConsistencyLevel <- WriteConstLevel,
            \* Don't model data loss. It is not needed, and it allows a session
            \* token to expire after being acquired. Handling that would
            \* complicate this spec.
            epoch <- 1
 
 Read(t, k) ==
    IF "RCL" \notin DOMAIN IOEnv THEN DB!StrongConsistencyRead(k)
    ELSE
        CASE IOEnv.RCL = "strong" -> DB!StrongConsistencyRead(k)
        []  IOEnv.RCL = "session" -> DB!SessionConsistencyRead(t, k)
        []  IOEnv.RCL = "eventual" -> DB!EventualConsistencyRead(k)

---------------------------------------------------------------------

Nil == DB!NoSessionToken

TypesOK == DB!TypesOK

VARIABLE messageQueue, future, backendValue, requests

specVars == <<messageQueue, future, backendValue, requests>>
vars == <<dbVars, specVars>>

Init ==
    /\ messageQueue = <<>>
    /\ future = Nil
    /\ backendValue = NoValue
    /\ requests = Values
    /\ DB!Init

1FrontendWrite ==
    /\ future = Nil
    /\ \E val \in requests: DB!WriteInit("k", val, LAMBDA t: future' = t)
    /\ UNCHANGED <<dbVarsExceptLog, requests, messageQueue, backendValue>>

3FrontendEnqueue ==
    /\ future # Nil
    /\ DB!WriteSucceed(future)
    /\ requests' = requests \ { future.value }
    /\ messageQueue' = << [ k |-> "k", t |-> future ] >>
    /\ UNCHANGED <<dbVars, future, backendValue>>

5BackendRead ==
    /\ messageQueue # <<>>
    /\ messageQueue' = Tail(messageQueue)
    /\ \E read \in
            Read(Head(messageQueue).t, Head(messageQueue).k) :
                backendValue' = read.value
    /\ UNCHANGED <<dbVars, requests, future>>

cosmos ==
    /\ DB!Next
    /\ UNCHANGED specVars

Next ==
    \/ 1FrontendWrite
    \/ 3FrontendEnqueue
    \/ 5BackendRead
    \/ cosmos

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(5BackendRead)

----------------------------------------------------------------------------

WorkerReceivesCorrectValue ==
    \A val \in Values:
        val \notin requests ~> backendValue = val

====
