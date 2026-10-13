---- MODULE MC ----
EXTENDS trashbins, TLC

\* CONSTANT definitions @modelParameterConstants:0NumUsers
const_179192912148854000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1NumTrucks
const_179192912148955000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2MaxCapacity
const_179192912148956000 == 
7
----

\* CONSTANT definitions @modelParameterConstants:3MaxUserTrash
const_179192912148957000 == 
4
----

\* CONSTANT definitions @modelParameterConstants:4NumBins
const_179192912148958000 == 
1
----

\* INVARIANT definition @modelCorrectnessInvariants:8
inv_179192912148967000 ==
truckCommand.command /= "request"
----
=============================================================================
\* Modification History
\* Created Wed Oct 14 00:05:21 CEST 2026 by nasteapopova
