----- MODULE Frob -----
EXTENDS Sequences, Naturals, TLC

Null == "null"

log == 
<< 
   [data |-> 1, type |-> "Write", consistency |-> [lsn |-> 1, level |-> "Strong"], doc |-> "doc1", old |-> Null, region |-> "R", orig |-> 1],
   [type |-> "Read", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc1", region |-> "R", orig |-> 1],
   [type |-> "Read", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc1", region |-> "S", orig |-> 2],

   [data |-> 3, type |-> "Write", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc2", old |-> Null, region |-> "R", orig |-> 2],
   [type |-> "Read", consistency |-> [lsn |-> 4, level |-> "Session"], doc |-> "doc1", region |-> "R", orig |-> 2],
   
   [data |-> 5, type |-> "Write", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc1", old |-> Null, region |-> "R", orig |-> 2],
   [type |-> "Read", consistency |-> [lsn |-> 6, level |-> "Session"], doc |-> "doc1", region |-> "R", orig |-> 2], \* This read observes the writes here.
   
   [data |-> 7, type |-> "Write", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc1", old |-> Null, region |-> "R", orig |-> 2],
   [type |-> "Read", consistency |-> [lsn |-> 8, level |-> "Session"], doc |-> "doc1", region |-> "R", orig |-> 2],
   
   [data |-> 9, type |-> "Write", consistency |-> [lsn |-> 1, level |-> "Session"], doc |-> "doc1", old |-> Null, region |-> "R", orig |-> 2]
>>

writeRegion == "R"

MySelectSeq(s, Test(_)) == 
  LET F[i \in 0..Len(s)] == 
        IF i = 0 THEN << >>
                 ELSE IF Test(i) THEN Append(F[i-1], s[i])
                                    ELSE F[i-1]
  IN F[Len(s)]

Pred(i) ==
    \* Do we keep all the reads?
    \* No, because that would mean we keep reads of writes that are removed
    \* (a read in the write region of a write that is going to be lost).
    \* \/ log[i].type = "Read"
    \/ /\ log[i].type = "Write"
       /\ \E j \in i..Len(log) :
            /\ log[j].type = "Read"
            /\ log[j].doc = log[i].doc
            /\ log[j].region # log[i].region

prefixOff ==
    MySelectSeq(log, Pred)

prefix ==
    \* We probably have to do this for each doc. 
    { i \in 1..Len(log):
        /\ log[i].type = "Write"
        /\ \E j \in i..Len(log) :
            /\ log[j].type = "Read"
            /\ log[j].doc = log[i].doc
            /\ log[j].region # log[i].region }

ASSUME PrintT(prefix)

======





\* Idea:

lsn ==
    \* This spec assumes a reliable global sequencer.
    Nat

docs ==
    {"doc1", "doc2"}

log ==
    Seq(WriteRequests)

db ==
    [ docs -> log]

Observed ==
    [WriteRequests -> {ReadRequests}]
