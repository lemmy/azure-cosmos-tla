---- MODULE show521677simple ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
 CONSTANTS VersionBound, StalenessBound

 VARIABLES log, commitIndex, readIndex

 Keys == {"k1"}
 Values == {"v1","v2"}
 NoValue == "NoValue"

 dbVarsExceptLog == <<commitIndex, readIndex>>
 dbVars == <<dbVarsExceptLog, log>>

 DB == INSTANCE CosmosDB WITH
            WriteConsistencyLevel <- StrongConsistency,
            \* Don't model data loss. It is not needed, and it allows a session
            \* token to expire after being acquired. Handling that would
            \* complicate this spec.
            epoch <- 1

---------------------------------------------------------------------

NoSessionToken == DB!NoSessionToken

TypesOK == DB!TypesOK

VARIABLE serviceBus, frontendToken, backendValue, requests, pending

specVars == <<serviceBus, frontendToken, backendValue, requests, pending>>
vars == <<dbVars, specVars>>

Init ==
    /\ serviceBus = <<>>
    /\ frontendToken = NoSessionToken
    /\ backendValue = NoValue
    /\ pending = NoValue
    /\ requests = Values
    /\ DB!Init

1FrontendWrite ==
    /\ pending = NoValue
    /\ frontendToken = NoSessionToken
    /\ \E val \in requests: 
        /\ DB!WriteInit("k1", val)
        /\ pending' = val
    /\ frontendToken' = DB!WriteInitToken
    /\ UNCHANGED <<dbVarsExceptLog, requests, serviceBus, backendValue>>

3FrontendEnqueue ==
    /\ pending # NoValue
    /\ serviceBus = <<>>
    /\ frontendToken # NoSessionToken
    /\ DB!WriteCanSucceed(frontendToken)
    /\ requests' = requests \ { pending }
    /\ pending' = NoValue
    /\ serviceBus' = << [ k |-> "k1", t |-> frontendToken ] >>
    /\ UNCHANGED <<dbVars, frontendToken, backendValue>>

5BackendRead ==
    /\ serviceBus # <<>>
    /\ serviceBus' = Tail(serviceBus)
    /\ \E read \in
            DB!SessionConsistencyRead(Head(serviceBus).t, Head(serviceBus).k) :
            \* DB!StrongConsistencyRead(Head(serviceBus).k) :
            \* DB!EventualConsistencyRead(Head(serviceBus).k) :
                backendValue' = read.value
    /\ UNCHANGED <<dbVars, requests, pending, frontendToken>>

cosmos ==
    /\ DB!Next
    /\ UNCHANGED specVars

Next ==
    \/ 1FrontendWrite
    \/ 3FrontendEnqueue
    \/ 5BackendRead
    \/ cosmos

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(1FrontendWrite \/ 3FrontendEnqueue)
        /\ WF_vars(5BackendRead)
        /\ WF_vars(cosmos)

----------------------------------------------------------------------------

WorkerReceivesCorrectValue ==
    \A val \in Values:
        (val \notin requests) ~> backendValue = val

====
