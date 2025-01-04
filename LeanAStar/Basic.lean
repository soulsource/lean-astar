import BinaryHeap
import LeanAStar.Finite
import LeanAStar.HashSet

namespace LeanAStar

/-- The type-class any node type needs to implement in order to be usable in AStar -/
class AStarNode.{u, v} (α : Type u) extends Finite α, Hashable α, BEq α where
  Costs : Type v
  costsLe : Costs → Costs → Bool
  costs_order : BinaryHeap.TotalAndTransitiveLe costsLe
  getNeighbours : α → List (α × Costs)
  isGoal : α → Bool
  remaining_costs_heuristic : α → Costs

protected structure OpenSetEntry (α : Type u) [AStarNode α] where
  node : α
  accumulated_costs : AStarNode.Costs α
  estimated_total_costs : AStarNode.Costs α

protected def OpenSetEntry.le {α : Type u} [AStarNode α] (a b : LeanAStar.OpenSetEntry α) : Bool :=
  AStarNode.costsLe a.estimated_total_costs b.estimated_total_costs

protected def OpenSetEntry.le_total {α : Type u} [AStarNode α] : BinaryHeap.total_le (α := LeanAStar.OpenSetEntry α) OpenSetEntry.le :=
  λa b ↦ AStarNode.costs_order.right a.estimated_total_costs b.estimated_total_costs

protected def OpenSetEntry.le_trans {α : Type u} [AStarNode α] : BinaryHeap.transitive_le (α := LeanAStar.OpenSetEntry α) OpenSetEntry.le :=
  λa b c ↦ AStarNode.costs_order.left a.estimated_total_costs b.estimated_total_costs c.estimated_total_costs

protected def findFirstNotInClosedSet {α : Type u} [AStarNode α] {n : Nat} (openSet : BinaryHeap (LeanAStar.OpenSetEntry α) OpenSetEntry.le n) (closedSet : Std.HashSet α) : Option ((r : Nat) × LeanAStar.OpenSetEntry α × BinaryHeap (LeanAStar.OpenSetEntry α) OpenSetEntry.le r) :=
  match n, openSet with
  | 0, _ => none
  | m+1, openSet =>
    let (openSetEntry, openSet) := openSet.pop
    if closedSet.contains openSetEntry.node then
      LeanAStar.findFirstNotInClosedSet openSet closedSet
    else
      some ⟨m, openSetEntry, openSet⟩

protected theorem findFirstNotInClosedSet_not_in_closed_set {α : Type u} [AStarNode α] {n : Nat} (openSet : BinaryHeap (LeanAStar.OpenSetEntry α) OpenSetEntry.le n) (closedSet : Std.HashSet α) {result : (r : Nat) × LeanAStar.OpenSetEntry α × BinaryHeap (LeanAStar.OpenSetEntry α) OpenSetEntry.le r} (h₁ : LeanAStar.findFirstNotInClosedSet openSet closedSet = some result) : ¬closedSet.contains result.snd.fst.node := by
  simp
  unfold LeanAStar.findFirstNotInClosedSet at h₁
  split at h₁; contradiction
  simp at h₁
  split at h₁
  case h_2.isTrue =>
    have h₃ := LeanAStar.findFirstNotInClosedSet_not_in_closed_set _ closedSet h₁
    simp at h₃
    assumption
  case h_2.isFalse h₂ =>
    simp at h₂ h₁
    subst result
    assumption

protected def findPath_Aux {α : Type u} [AStarNode α] [Add (AStarNode.Costs α)] [LawfulBEq α] {n : Nat} (openSet : BinaryHeap (LeanAStar.OpenSetEntry α) OpenSetEntry.le n) (closedSet : Std.HashSet α) : Option (AStarNode.Costs α) :=
  match _h₁ : LeanAStar.findFirstNotInClosedSet openSet closedSet with
  | none => none
  | some ⟨_,({node, accumulated_costs,..}, openSet)⟩ =>
    if AStarNode.isGoal node then
      some accumulated_costs
    else
      let neighbours := (AStarNode.getNeighbours node).filter (not ∘ closedSet.contains ∘ Prod.fst)
      let newClosedSet := closedSet.insert node
      let openSet := openSet.pushList
        $ (λ (node, costs) ↦
          let accumulated_costs := accumulated_costs + costs
          let estimated_total_costs := accumulated_costs + AStarNode.remaining_costs_heuristic node
          {node, accumulated_costs, estimated_total_costs := estimated_total_costs : LeanAStar.OpenSetEntry α}
          )
        <$> neighbours
      LeanAStar.findPath_Aux openSet newClosedSet
termination_by (Finite.cardinality α) - closedSet.size
decreasing_by
  have h₃ := Std.HashSet.size_insert (m := closedSet) (k := node)
  split at h₃
  case isTrue =>
    have := LeanAStar.findFirstNotInClosedSet_not_in_closed_set _ _ _h₁
    contradiction
  case isFalse h₂ =>
    rw[h₃]
    have : closedSet.size < (Finite.cardinality α) := Std.HashSet.size_lt_finite_cardinality_of_not_mem closedSet ⟨_,h₂⟩
    omega

structure StartPoint (α : Type u) [AStarNode α] where
  start : α
  initial_costs : AStarNode.Costs α

protected structure PathFindCosts (α : Type u) [AStarNode α] where
  previousNodes : List α
  actualCosts : AStarNode.Costs α

protected structure PathFindCostsAdapter (α : Type u) [AStarNode α] where
  node : α

private theorem Function.comp_assoc {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} (f : γ → δ) (g : β → γ) (h : α → β) : f ∘ g ∘ h = (f ∘ g) ∘ h := rfl
private theorem Function.comp_id_neutral_left {α : Type u} {β : Type v} (f : α → β) : id ∘  f = f := rfl

protected instance {α : Type u} [AStarNode α] : AStarNode (LeanAStar.PathFindCostsAdapter α) where
  cardinality := Finite.cardinality α
  enumerate := Finite.enumerate ∘ PathFindCostsAdapter.node
  nth := PathFindCostsAdapter.mk ∘ Finite.nth
  nth_inverse_enumerate := by
    rewrite[←Function.comp_assoc]
    rewrite (occs := .pos [2])[Function.comp_assoc]
    rewrite[Finite.nth_inverse_enumerate (α := α)]
    rfl
  enumerate_inverse_nth := by
    rewrite[←Function.comp_assoc]
    rewrite (occs := .pos [2])[Function.comp_assoc]
    have : PathFindCostsAdapter.node ∘ PathFindCostsAdapter.mk (α := α) = id := rfl
    rw[this, Function.comp_id_neutral_left]
    exact Finite.enumerate_inverse_nth
  hash := Hashable.hash ∘ PathFindCostsAdapter.node
  beq := λa b ↦ a.node == b.node
  Costs := LeanAStar.PathFindCosts α
  costsLe := λa b ↦ AStarNode.costsLe a.actualCosts b.actualCosts
  costs_order := ⟨λa b c ↦ AStarNode.costs_order.left a.actualCosts b.actualCosts c.actualCosts, λa b ↦ AStarNode.costs_order.right a.actualCosts b.actualCosts⟩
  getNeighbours := λx ↦
    (AStarNode.getNeighbours x.node).map λ(node, actualCosts) ↦ ({node},{previousNodes := [x.node], actualCosts})
  isGoal := AStarNode.isGoal ∘ PathFindCostsAdapter.node
  remaining_costs_heuristic := λx ↦
    {previousNodes := [x.node], actualCosts := AStarNode.remaining_costs_heuristic x.node}

protected instance {α : Type u} [AStarNode α] [Add (AStarNode.Costs α)] : Add (LeanAStar.PathFindCosts α) where
  add := λa b ↦
    {
      previousNodes := b.previousNodes ++ a.previousNodes
      actualCosts := a.actualCosts + b.actualCosts
    }

protected instance {α : Type u} [AStarNode α] [LawfulBEq α] : LawfulBEq (LeanAStar.PathFindCostsAdapter α) where
  rfl := by
    intro a
    cases a
    unfold BEq.beq AStarNode.toBEq LeanAStar.instAStarNodePathFindCostsAdapter
    simp only [beq_self_eq_true]
  eq_of_beq := by
    intros a b
    cases a
    cases b
    unfold BEq.beq AStarNode.toBEq LeanAStar.instAStarNodePathFindCostsAdapter
    simp only [beq_iff_eq, PathFindCostsAdapter.mk.injEq, imp_self]

/-- Returns the lowest-costs from any start to the nearest goal. -/
def findLowestCosts {α : Type u} [AStarNode α] [Add (AStarNode.Costs α)] [LawfulBEq α] (starts : List (StartPoint (α := α))) : Option (AStarNode.Costs α) :=
  let openSet := BinaryHeap.ofList ⟨OpenSetEntry.le_trans, OpenSetEntry.le_total⟩ $ starts.map λ{start, initial_costs}↦
    {node := start, accumulated_costs := initial_costs, estimated_total_costs:= AStarNode.remaining_costs_heuristic start : LeanAStar.OpenSetEntry α}
  LeanAStar.findPath_Aux openSet Std.HashSet.empty

/-- Helper to not only get the lowest costs, but also the shortest path. Could be implemented more efficient. -/
def findShortestPath {α : Type u} [AStarNode α] [Add (AStarNode.Costs α)] [LawfulBEq α] (starts : List (StartPoint (α := α))) : Option (AStarNode.Costs α × List α) :=
  let starts : List (StartPoint (α := LeanAStar.PathFindCostsAdapter α)) := starts.map λ{start, initial_costs} ↦
    {
      start := {node := start}
      initial_costs := {
        previousNodes := [start]
        actualCosts := initial_costs
      }
    }
  -- no idea why this is needed, but without this in the local context, the call to findLowerstCosts fails
  have : Add (LeanAStar.PathFindCosts α) := inferInstance
  let i := findLowestCosts starts
  i.map λ{previousNodes, actualCosts} ↦
    (actualCosts, previousNodes)
