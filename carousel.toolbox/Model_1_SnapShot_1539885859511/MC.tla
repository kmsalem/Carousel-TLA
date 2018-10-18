---- MODULE MC ----
EXTENDS carousel, TLC

\* CONSTANT definitions @modelParameterConstants:0N
const_1539885858493248000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NumOfMessages
const_1539885858493249000 == 
6
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1539885858493250000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1539885858493251000 ==
StatusInvariant
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1539885858493252000 ==
CounterInvariant
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1539885858493253000 ==
Termination
----
=============================================================================
\* Modification History
\* Created Thu Oct 18 14:04:18 EDT 2018 by dzklavier
