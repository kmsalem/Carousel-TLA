---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1539885122631230000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_1539885122631231000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1539885122631232000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539885122631233000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1539885122631234000 ==
CounterInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1539885122631235000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Thu Oct 18 13:52:02 EDT 2018 by dzklavier
