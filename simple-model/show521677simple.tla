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

\* cosmosTruncateLog ==
\*     /\ DB!TruncateLog
\*     /\ UNCHANGED specVars

\* cosmosIncreaseReadIndexAndOrCommitIndex ==
\*     /\ DB!IncreaseReadIndexAndOrCommitIndex
\*     /\ UNCHANGED specVars

cosmos ==
    /\ DB!Next
    /\ UNCHANGED specVars

Next ==
    \/ 1FrontendWrite
    \/ 3FrontendEnqueue
    \/ 5BackendRead
    \/ cosmos
    \* \/ cosmosTruncateLog
    \* \/ cosmosIncreaseReadIndexAndOrCommitIndex

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(1FrontendWrite \/ 3FrontendEnqueue)
        /\ WF_vars(5BackendRead)
        /\ WF_vars(cosmos)

----------------------------------------------------------------------------

WorkerReceivesCorrectValueOld ==
    [][Len(serviceBus) > Len(serviceBus')
        => backendValue' = "v1"]_vars

WorkerReceivesCorrectValueBroken ==
    \* This property does not hold because it doesn't suffice for the value to
    \* appear in the log.  The value has to be replicated, i.e., the commitIndex
    \* has to be incremented accordingly.  In other words, the write is not yet
    \* durable when the value appears in the log.
    \A val \in Values: 
        ((\E i \in 1..Len(log): 
            log[i].value = val) ~> backendValue = val)

WorkerReceivesCorrectValueTooStrong ==
    \A val \in Values: 
        (\E i \in 1..Len(log):
            \* A value is durable if it appears in the log and its log
             \* position is past the commitIndex.
            /\ log[i].value = val
            /\ commitIndex >= i) ~> backendValue = val

WorkerReceivesCorrectValue ==
    \A val \in Values:
        (val \notin requests) ~> backendValue = val

WorkDone ==
    []<><<5BackendRead>>_vars

View ==
    <<myepoch % 2, commitIndex, readIndex, log, specVars>>

Constraint ==
    myepoch < 4
====
