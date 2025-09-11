---------------------------- MODULE ShredTest ----------------------------
(*
Test module for Shred specification
This module extends Shred and adds some test scenarios
*)

EXTENDS Shred

\* Test helper functions

\* Create a sample valid shred
SampleShred1 ==
    CreateShred(1, 1, 1, FALSE, "root1", "data1", "path1", "sig1")

SampleShred2 ==
    CreateShred(1, 1, 2, FALSE, "root1", "data2", "path2", "sig2")

SampleShred3 ==
    CreateShred(1, 2, 1, TRUE, "root2", "data3", "path3", "sig3")

\* Test that sample shreds are valid
TestSampleShreddValid ==
    /\ IsValidShred(SampleShred1)
    /\ IsValidShred(SampleShred2) 
    /\ IsValidShred(SampleShred3)

\* Test that shreds with same position are detected
TestSamePosition ==
    LET shred1 == SampleShred1
        shred2 == CreateShred(1, 1, 1, TRUE, "root2", "data2", "path2", "sig2")
    IN SamePosition(shred1, shred2)

\* Test different positions
TestDifferentPositions ==
    ~SamePosition(SampleShred1, SampleShred2)

\* Test shred identifier
TestShredId ==
    ShredId(SampleShred1) = <<1, 1, 1>>

\* Test filtering by slice
TestGetShredsForSlice ==
    LET testShreds == {SampleShred1, SampleShred2, SampleShred3}
    IN LET slice11Shreds == {shred \in testShreds : 
                              shred.slot = 1 /\ shred.sliceIndex = 1}
       IN slice11Shreds = {SampleShred1, SampleShred2}

\* Combined test assertion
TestAssertions ==
    /\ TestSampleShreddValid
    /\ TestSamePosition
    /\ TestDifferentPositions
    /\ TestShredId
    /\ TestGetShredsForSlice

\* Property: Test assertions hold
THEOREM TestsPass == TestAssertions

=======================================================================