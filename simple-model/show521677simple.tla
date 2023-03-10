---- MODULE show521677simple ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS StrongConsistency, BoundedStaleness,
          SessionConsistency, ConsistentPrefix,
          EventualConsistency
 CONSTANTS VersionBound, StalenessBound

 VARIABLES log, commitIndex, readIndex

 Keys == {"taskKey"}
 Values == {"taskValue"}
 NoValue == "NoValue"

 dbVarsExceptLog == <<commitIndex, readIndex>>
 dbVars == <<dbVarsExceptLog, log>>

 DB == INSTANCE CosmosDB WITH
            WriteConsistencyLevel <- SessionConsistency,
            \* Don't model data loss. It is not needed, and it allows a session
            \* token to expire after being acquired. Handling that would
            \* complicate this spec.
            epoch <- 1

---------------------------------------------------------------------

NoSessionToken == DB!NoSessionToken

TypesOK == DB!TypesOK

VARIABLE serviceBus, frontendToken, backendValue

specVars == <<serviceBus, frontendToken, backendValue>>
vars == <<dbVars, specVars>>

Init ==
    /\ serviceBus = <<>>
    /\ frontendToken = NoSessionToken
    /\ backendValue = NoValue
    /\ DB!Init

1FrontendWrite ==
    /\ frontendToken = NoSessionToken
    /\ DB!WriteInit("taskKey", "taskValue")
    /\ frontendToken' = DB!WriteInitToken
    /\ UNCHANGED <<dbVarsExceptLog, serviceBus, backendValue>>

3FrontendEnqueue ==
    /\ serviceBus = <<>>
    /\ frontendToken # NoSessionToken
    /\ DB!WriteCanSucceed(frontendToken)
    /\ serviceBus' = << [ k |-> "taskKey", t |-> frontendToken ] >>
    /\ UNCHANGED <<dbVars, frontendToken, backendValue>>

5BackendRead ==
    /\ serviceBus # <<>>
    /\ serviceBus' = Tail(serviceBus)
    /\ \E read \in 
            DB!SessionConsistencyRead(Head(serviceBus).t, Head(serviceBus).k) :
                backendValue' = read.value
    /\ UNCHANGED <<dbVars, frontendToken>>

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

WorkerReceivesCorrectValue ==
    [][Len(serviceBus) > Len(serviceBus')
        => backendValue' = "taskValue"]_vars

====
