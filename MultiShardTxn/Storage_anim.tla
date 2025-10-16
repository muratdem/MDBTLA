---- MODULE Storage_anim ----
EXTENDS Sequences, Naturals, Integers, Util, TLC, Storage




\* 
\* Animation stuff.
\* 


\* Merge two records
Merge(r1, r2) == 
    LET D1 == DOMAIN r1 D2 == DOMAIN r2 IN
    [k \in (D1 \cup D2) |-> IF k \in D1 THEN r1[k] ELSE r2[k]]

SVGElem(_name, _attrs, _children, _innerText) == [name |-> _name, attrs |-> _attrs, children |-> _children, innerText |-> _innerText ]

Text(x, y, text, attrs) == 
    \* Text element.'x' and 'y' should be given as integers, and 'text' given as a string.
    LET svgAttrs == [x |-> x, 
                     y |-> y] IN
    SVGElem("text", Merge(svgAttrs, attrs), <<>>, text) 

\* Circle element. 'cx', 'cy', and 'r' should be given as integers.
Circle(cx, cy, r, attrs) == 
    LET svgAttrs == [cx |-> cx, 
                     cy |-> cy, 
                     r  |-> r] IN
    SVGElem("circle", Merge(svgAttrs, attrs), <<>>, "")

\* Rectangle element. 'x', 'y', 'w', and 'h' should be given as integers.
Rect(x, y, w, h, attrs) == 
    LET svgAttrs == [x      |-> x, 
                     y      |-> y, 
                     width  |-> w, 
                     height |-> h] IN
    SVGElem("rect", Merge(svgAttrs, attrs), <<>>, "")

Image(x, y, width, height, href, attrs) == 
    LET svgAttrs == ("xlink:href" :> href @@
                     "x"         :> x @@
                     "y"         :> y @@
                     "width"     :> width @@
                     "height"    :> height) IN
    SVGElem("image", Merge(svgAttrs, attrs), <<>>, "")

Line(x1, y1, x2, y2, attrs) == 
    (**************************************************************************)
    (* Line element.  'x1', 'y1', 'x2', and 'y2' should be given as integers. *)
    (**************************************************************************)
    LET svgAttrs == [x1 |-> x1, 
                     y1 |-> y1, 
                     x2 |-> x2,
                     y2 |-> y2] IN
    SVGElem("line", Merge(svgAttrs, attrs), <<>>, "")

\* Group element. 'children' is as a sequence of elements that will be contained in this group.
Group(children, attrs) == SVGElem("g", attrs, children, "")

\* Edges can also be specified as tuples of length > 2, such as <<n1,n2,x,y,z>>,
\* which defines an edge between n1 -> n2, but x,y,z define additional metadata
\* specific to that edge e.g. this also allows for multiple edges between the
\* same nodes in the same direction, but with potentially different edge
\* "types".
DiGraph(V, E, nodeAttrsFn, edgeAttrsFn) == SVGElem("digraph", [V |-> V, E |-> E, nodeAttrsFn |-> nodeAttrsFn, edgeAttrsFn |-> edgeAttrsFn], <<>>, "")

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* ---------------------------------------------
\* Animation derived from Storage.tla state
\* ---------------------------------------------

IndexOf(seq, elem) == CHOOSE i \in DOMAIN seq : seq[i] = elem

\* Sequence of nodes (for deterministic layout)
NodeSeq == SetToSeq(Node)

\* Compute a readable label for a single log entry
LogEntryLabel(e) ==
    LET kind == IF "prepare" \in DOMAIN e THEN "prepare" ELSE "commit"
        tid  == IF "tid" \in DOMAIN e THEN e.tid ELSE -1
        ts   == IF "ts" \in DOMAIN e THEN e.ts ELSE -1
        dur  == IF "durableTs" \in DOMAIN e THEN e.durableTs ELSE 0
    IN ToString(kind) \o " tid=" \o ToString(tid) \o " ts=" \o ToString(ts) \o (IF dur # 0 THEN (" dur=" \o ToString(dur)) ELSE "")

\* Render log of a node n as a vertical list
NodeLogElem(n, ox, oy) ==
    LET entries == mlog[n]
        lines == [ i \in DOMAIN entries |->
                    LET y == oy + 16*i
                        label == LogEntryLabel(entries[i])
                    IN Text(ox, y, label, ("font-size" :> "10px")) ]
    IN Group(<<Text(ox, oy, "mlog[" \o ToString(n) \o "]", ("font-weight" :> "bold"))>> \o SetToSeq(Range(lines)), <<>>)

\* Render timestamps for a node n
NodeTsElem(n, ox, oy) ==
    Group(<<
        Text(ox, oy, "stableTs=" \o ToString(stableTs[n]), ("fill" :> "#444" @@ "font-size" :> "10px")),
        Text(ox, oy+14, "oldestTs=" \o ToString(oldestTs[n]), ("fill" :> "#444" @@ "font-size" :> "10px")),
        Text(ox, oy+28, "allDurableTs=" \o ToString(allDurableTs[n]), ("fill" :> "#444" @@ "font-size" :> "10px"))
    >>, <<>>)

\* Determine a concise status string for a txn at node n
TxnStatusStr(n, tid) ==
    IF mtxnSnapshots[n][tid].committed THEN "committed"
    ELSE IF mtxnSnapshots[n][tid].aborted THEN "aborted"
    ELSE IF mtxnSnapshots[n][tid].active /\ ~mtxnSnapshots[n][tid].prepared THEN "active"
    ELSE IF "prepared" in DOMAIN mtxnSnapshots[n][tid] THEN "prepared"
    ELSE "idle"

\* Render active/known transactions at node n
NodeTxnsElem(n, ox, oy) ==
    LET tids == SetToSeq(MTxId)
        rows == [ i \in DOMAIN tids |->
                  LET tid == tids[i]
                      y == oy + 14*i
                      snap == mtxnSnapshots[n][tid]
                      status == TxnStatusStr(n, tid)
                      tsStr == IF "ts" \in DOMAIN snap THEN ToString(snap.ts) ELSE "-"
                      prepStr == IF snap.prepared THEN "/ prepTs=" \o ToString(snap.prepareTs) ELSE ""
                      label == "txn " \o ToString(tid) \o ": " \o status \o (IF snap.active THEN (" ts=" \o tsStr \o prepStr) ELSE "")
                  IN Text(ox, y, label, ("font-size" :> "10px")) ]
    IN Group(<<Text(ox, oy, "txns[" \o ToString(n) \o "]", ("font-weight" :> "bold"))>> \o SetToSeq(Range(rows)), <<>>)

\* Layout for a single node panel
NodePanel(n, idx) ==
    LET baseX == 20 + 360*(idx-1)
        baseY == 20
    IN Group(<<
        Rect(baseX-10, baseY-10, 340, 220, ("fill" :> "#f9f9f9" @@ "stroke" :> "#ddd")),
        Text(baseX, baseY-20, "Node " \o ToString(n), ("font-weight" :> "bold")),
        NodeTsElem(n, baseX, baseY),
        NodeLogElem(n, baseX, baseY+50),
        NodeTxnsElem(n, baseX+180, baseY)
    >>, <<>>)

\* Top-level animation view aggregating all nodes
AnimView ==
    LET nodes == NodeSeq
        panels == [ i \in DOMAIN nodes |-> NodePanel(nodes[i], i) ]
    IN Group(SetToSeq(Range(panels)), [transform |-> "translate(0, 0) scale(1.0)"])


===============================================================================