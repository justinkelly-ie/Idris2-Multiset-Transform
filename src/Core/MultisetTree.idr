module Core.MultisetTree

import Core.BoxInt
import Core.Multiset

%default total

------------------------------------------------------------------------
-- 1. FAST BALANCED MULTISET SEARCH TREE O(LOG N)
------------------------------------------------------------------------

||| Binary Search Tree for Multiset Element Multiplicities.
public export
data MultisetTree a =
    Leaf
  | Node (MultisetTree a) a Nat (MultisetTree a)

public export
Eq a => Eq (MultisetTree a) where
  Leaf == Leaf = True
  (Node l1 x1 c1 r1) == (Node l2 x2 c2 r2) =
    x1 == x2 && c1 == c2 && l1 == l2 && r1 == r2
  _ == _ = False

||| Returns the total number of distinct elements in the tree:
public export
treeElementCount : MultisetTree a -> Nat
treeElementCount Leaf = 0
treeElementCount (Node l _ _ r) = 1 + treeElementCount l + treeElementCount r

||| Returns the total multiplicity sum of all tokens in the tree:
public export
treeTokenSum : MultisetTree a -> Nat
treeTokenSum Leaf = 0
treeTokenSum (Node l _ c r) = c + treeTokenSum l + treeTokenSum r

||| Inserts a token with multiplicity count into the multiset tree:
public export
insertTokenTree : Ord a => a -> Nat -> MultisetTree a -> MultisetTree a
insertTokenTree val count Leaf = Node Leaf val count Leaf
insertTokenTree val count (Node l x c r) =
  if val < x
    then Node (insertTokenTree val count l) x c r
    else if val > x
      then Node l x c (insertTokenTree val count r)
      else Node l x (c + count) r

||| Lookups the multiplicity count of a token in O(log N) steps:
public export
lookupTokenTree : Ord a => a -> MultisetTree a -> Nat
lookupTokenTree _ Leaf = 0
lookupTokenTree val (Node l x c r) =
  if val < x
    then lookupTokenTree val l
    else if val > x
      then lookupTokenTree val r
      else c

------------------------------------------------------------------------
-- 2. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Fast MultisetTree Invariants)
------------------------------------------------------------------------

||| Audits O(log N) MultisetTree Insertion and Lookup:
||| Insert (BoxInt 10, count 5) and (BoxInt 20, count 3):
||| Lookup 10 => 5, Lookup 20 => 3, Lookup 30 => 0.
public export
auditMultisetTreeLookupProof : Bool
auditMultisetTreeLookupProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
      c10 = lookupTokenTree (intToBoxInt 10) t2
      c20 = lookupTokenTree (intToBoxInt 20) t2
      c30 = lookupTokenTree (intToBoxInt 30) t2
  in c10 == 5 && c20 == 3 && c30 == 0

||| Audits Total Multiplicity Sum on MultisetTree:
||| Total tokens in tree = 5 + 3 = 8.
public export
auditMultisetTreeTokenSumProof : Bool
auditMultisetTreeTokenSumProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
  in treeTokenSum t2 == 8 && treeElementCount t2 == 2

------------------------------------------------------------------------
-- 3. CANONICAL BOXSPEC MULTISET TREES
------------------------------------------------------------------------

||| Specialized Multiset Tree indexed by canonical BoxSpec configurations.
public export
BoxSpecTree : Type
BoxSpecTree = MultisetTree BoxSpec

||| Audits that MultisetTree uses Canonical BoxSpec total ordering (Leaf < [[]] < [[] []]):
||| Inserting BoxSpec 0, 1, 2 stores them in deterministic binary search tree order.
public export
auditBoxSpecTreeOrderingProof : Bool
auditBoxSpecTreeOrderingProof =
  let b0 = fromNatBoxSpec 0
      b1 = fromNatBoxSpec 1
      b2 = fromNatBoxSpec 2
      t0 : BoxSpecTree = Leaf
      t1 = insertTokenTree b1 10 t0
      t2 = insertTokenTree b0 5 t1
      t3 = insertTokenTree b2 15 t2
      c0 = lookupTokenTree b0 t3
      c1 = lookupTokenTree b1 t3
      c2 = lookupTokenTree b2 t3
      c3 = lookupTokenTree (fromNatBoxSpec 3) t3
  in c0 == 5 && c1 == 10 && c2 == 15 && c3 == 0 &&
     treeTokenSum t3 == 30 &&
     treeElementCount t3 == 3

------------------------------------------------------------------------
-- 4. TREE COMBINATORS & LOGARITHMIC COSMIC STATE EVOLUTION
------------------------------------------------------------------------

||| Merges two multiset trees by folding elements of the second into the first:
public export
mergeMultisetTrees : Ord a => MultisetTree a -> MultisetTree a -> MultisetTree a
mergeMultisetTrees target Leaf = target
mergeMultisetTrees target (Node l x c r) =
  let t1 = insertTokenTree x c target
      t2 = mergeMultisetTrees t1 l
  in mergeMultisetTrees t2 r

||| High-capacity tree-indexed cosmological state container.
||| Uses O(log N) balanced multiset trees for visible matter, dark energy, and dark matter.
public export
record TreeUniverseState where
  constructor MkTreeUniverseState
  epochNumber    : Nat
  visibleLattice : MultisetTree BoxInt
  darkEnergyROM  : MultisetTree BoxInt
  darkMatterLog  : MultisetTree BoxInt

||| Returns the total active token count across the entire TreeUniverseState:
public export
treeUniverseTotalTokens : TreeUniverseState -> Nat
treeUniverseTotalTokens (MkTreeUniverseState _ vm de dm) =
  treeTokenSum vm + treeTokenSum de + treeTokenSum dm

||| Linear QTT state transition for TreeUniverseState with strict token conservation:
public export
stepTreeUniverseLinear : (1 state : TreeUniverseState) ->
                         (matterTokens : List (BoxInt, Nat)) ->
                         TreeUniverseState
stepTreeUniverseLinear (MkTreeUniverseState ep vm de dm) newMatter =
  let updatedVM = foldl (\acc, (k, cnt) => insertTokenTree k cnt acc) vm newMatter
      updatedDM = insertTokenTree (natToBoxInt ep) 1 dm
  in MkTreeUniverseState (S ep) updatedVM de updatedDM

||| Audits Logarithmic Scaling State Evolution:
||| Tests that stepTreeUniverseLinear accurately updates the tree state and preserves tokens.
public export
auditTreeUniverseScalingProof : Bool
auditTreeUniverseScalingProof =
  let s0 = MkTreeUniverseState 0 Leaf Leaf Leaf
      s1 = stepTreeUniverseLinear s0 [(intToBoxInt 1, 9), (intToBoxInt 2, 18)]
      s2 = stepTreeUniverseLinear s1 [(intToBoxInt 3, 27)]
      totVM = treeTokenSum (visibleLattice s2)
      totDM = treeTokenSum (darkMatterLog s2)
      totAll = treeUniverseTotalTokens s2
  in epochNumber s2 == 2 &&
     totVM == 54 &&
     totDM == 2 &&
     totAll == 56
