---------------------------- MODULE Common ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

Max(S) ==
    CHOOSE x \in S : \A y \in S : x >= y

Min(S) ==
    CHOOSE x \in S : \A y \in S : x <= y

Range(f) ==
    {f[x] : x \in DOMAIN f}

MapKeys(m) ==
    DOMAIN m

MapValues(m) ==
    Range(m)

IsEmpty(S) ==
    S = {}

NonEmpty(S) ==
    S # {}

SingletonSet(x) ==
    {x}

PowerSetUpTo(S, n) ==
    {T \in SUBSET S : Cardinality(T) <= n}

RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

SeqToSet(seq) ==
    {seq[i] : i \in 1..Len(seq)}

AllDistinct(seq) ==
    \A i, j \in 1..Len(seq) : i # j => seq[i] # seq[j]

=======================================================================