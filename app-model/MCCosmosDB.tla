---- MODULE MCCosmosDB -----
EXTENDS CosmosDB

clients ==
    {1,2}
        
data ==
    Nat

regions ==
    {"R"}
        
MaxRequest ==
    \* /\ BagCardinality(inbox) < 5
    /\ Len(database) < 15

IsEven(n) ==
    n % 2 = 0

Level ==
    \* TRUE
    \* TLCGet("level") < 21
    /\ Len(database) < 10
    \* /\ ~IsEven(LastData)

Consistent ==
    \* This is not a theorem, because clients write non-monotonic data (values)
    \* into Cosmos.
    \* TODO: State this in terms of each doc's (partition) LSN.
    \A i,j \in 1..Len(database):
        (i < j /\ database[i].type = "Write" /\ database[j].type = "Write" )
        => (database[i].data) <= (database[j].data)
        \* => Len(database[i].data) <= Len(database[j].data)

NoErrorInPerpetuity ==
    <>[](\A c \in Clients: pc[c] # "error")

NoReceiveInPerpetuity ==
    <>[](\A c \in Clients: pc[c] # "receive")
    
Progress ==
    <>[](LastData("doc1") = 10)

Docs ==
    LET Writes == { w \in Range(database): w.type = "Write" }
    IN { w.doc : w \in Writes}

Alias ==
    [
        client |-> client,
        database |-> database,
        inbox |-> inbox,
        outbox |-> outbox,
        pc |-> pc,
        session |-> session,
        kv |-> [ d \in Docs |-> LastData(d) ]
    ]
======