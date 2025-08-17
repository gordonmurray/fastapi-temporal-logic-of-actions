----------------------------- MODULE Uploads_fixed ---------------------------
EXTENDS FiniteSets

CONSTANTS Contents

VARIABLES objects

TypeOK == objects \subseteq [content: Contents, key: Contents]

Init == objects = {}

\* Deterministic key: use the content itself as the key (models hashing)
UploadDet ==
  \E content \in Contents :
    /\ objects' = objects \cup {[content |-> content, key |-> content]}

Next == UploadDet

AtMostOneKeyPerContent ==
  \A object1, object2 \in objects : object1.content = object2.content => object1.key = object2.key

Spec == Init /\ [][Next]_objects
THEOREM Good == Spec => [] (TypeOK /\ AtMostOneKeyPerContent)
=============================================================================
