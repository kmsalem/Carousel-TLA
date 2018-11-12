---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_154117007264437000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2C
const_154117007264438000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3N
const_154117007264439000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154117007264440000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154117007264441000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154117007264442000 ==
SentReceivedInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154117007264443000 ==
CounterCorrectness
----
=============================================================================
\* Modification History
\* Created Fri Nov 02 10:47:52 EDT 2018 by dzklavier
