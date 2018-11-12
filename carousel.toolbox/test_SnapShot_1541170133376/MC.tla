---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_154117013029244000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:2C
const_154117013029245000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:3N
const_154117013029246000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154117013029247000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154117013029248000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_154117013029249000 ==
SentReceivedInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154117013029250000 ==
CounterCorrectness
----
=============================================================================
\* Modification History
\* Created Fri Nov 02 10:48:50 EDT 2018 by dzklavier
