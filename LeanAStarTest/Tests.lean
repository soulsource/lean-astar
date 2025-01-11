import LeanAStar

namespace LeanAStarTests

private structure TwoDArray (α : Type) where
  width : Nat
  height : Nat
  data : Array α
  valid : data.size = width * height

private structure TwoDArray.Coordinate (a : TwoDArray α) where
  x : Fin a.width
  y : Fin a.height
deriving Repr

instance : Hashable (TwoDArray.Coordinate a) where
  hash := λc ↦ mixHash (Hashable.hash c.x) (Hashable.hash c.y)

instance : BEq (TwoDArray.Coordinate a) where
  beq := λa b ↦ a.x == b.x && a.y == b.y

instance : LawfulBEq (TwoDArray.Coordinate a) where
  rfl := λ{a} ↦ by simp only [BEq.beq, decide_true, Bool.and_self]
  eq_of_beq := λ{a b} h₁ ↦ by cases a; cases b; simp only [BEq.beq, Bool.and_eq_true,
    decide_eq_true_eq] at h₁; simp only [h₁]

private theorem two_d_coordinate_to_index_lt_size {x y w h: Nat} (h₁ : x < w) (h₂ : y < h) : x + w*y < w*h :=
  Nat.le_pred_of_lt h₂
  |> Nat.mul_le_mul_left w
  |> Nat.add_le_add_iff_right.mpr
  |> (Nat.mul_pred w h).subst (motive :=λx↦w * y + w ≤ x + w)
  |> (Nat.sub_add_cancel (Nat.le_mul_of_pos_right w (Nat.zero_lt_of_lt h₂))).subst
  |> (Nat.add_comm _ _).subst (motive := λx↦x ≤ w*h)
  |> Nat.le_sub_of_add_le
  |> Nat.lt_of_lt_of_le h₁
  |> λx↦(Nat.add_lt_add_right) x (w * y)
  |> (Nat.sub_add_cancel (Nat.le_of_lt ((Nat.mul_lt_mul_left (Nat.zero_lt_of_lt h₁)).mpr h₂))).subst

private def TwoDArray.Coordinate.toIndex (co: TwoDArray.Coordinate a) : Fin (a.width*a.height) :=
  ⟨co.x.val + a.width*co.y.val,
    have h₁ : co.x.val < a.width := co.x.isLt
    have h₂ : co.y.val < a.height := co.y.isLt
    two_d_coordinate_to_index_lt_size h₁ h₂
  ⟩

private def TwoDArray.Coordinate.ofIndex {a : TwoDArray α} (index : Fin (a.width * a.height)) : a.Coordinate :=
  have : a.width > 0 :=
    have := index.isLt
    match h : a.width with
    | Nat.zero => absurd ((Nat.zero_mul a.height).subst (h.subst (motive := λx↦index<x*a.height) this)) (Nat.not_lt_zero index.val)
    | Nat.succ ww => Nat.succ_pos ww
  {
    x := ⟨index.val % a.width, Nat.mod_lt index.val this⟩
    y := ⟨index.val / a.width, Nat.div_lt_of_lt_mul index.isLt⟩
  }

private theorem TwoDArray.Coordinate.toIndex_inv_ofIndex {a : TwoDArray α} (index : Fin (a.width * a.height)) : TwoDArray.Coordinate.toIndex (TwoDArray.Coordinate.ofIndex index) = index := by
  simp only [TwoDArray.Coordinate.toIndex, TwoDArray.Coordinate.ofIndex, Nat.mod_add_div, Fin.eta]

private theorem Nat.pos_of_lt {a b : Nat} (h₁ : a < b) : 0 < b :=
  match a with
  | 0 => h₁
  | Nat.succ aa => Nat.pos_of_lt $ Nat.lt_trans (Nat.lt_succ_self aa) h₁

private theorem TwoDArray.Coordinate.ofIndex_inv_toIndex {a : TwoDArray α} (c : a.Coordinate) : TwoDArray.Coordinate.ofIndex (TwoDArray.Coordinate.toIndex c) = c := by
  unfold TwoDArray.Coordinate.toIndex TwoDArray.Coordinate.ofIndex
  simp only [Nat.add_mul_mod_self_left]
  congr
  case e_x.e_val => simp only [Fin.is_lt, Nat.mod_eq_of_lt]
  case e_y.e_val =>
    rw[Nat.add_mul_div_left]
    simp[Nat.div_eq_of_lt]
    exact Nat.pos_of_lt c.x.isLt

private def TwoDArray.Coordinate.toNats : TwoDArray.Coordinate a → Nat × Nat
| {x, y} => (x, y)

instance : GetElem (TwoDArray α) (TwoDArray.Coordinate a) α (λc _ ↦ a = c) where
  getElem := λa co h₁ ↦
    let idx : Fin (a.width * a.height) := h₁▸co.toIndex
    a.data[a.valid▸idx]

instance : Functor TwoDArray where
  map := λf b ↦ {b with data := b.data.map f, valid := (Array.size_map f b.data)▸b.valid}

private theorem TwoDArray.Coordinate.map_size (arr : TwoDArray α) (f : α → β) : (Functor.map f arr).width = arr.width ∧ (Functor.map f arr).height = arr.height := ⟨rfl, rfl⟩

private inductive Tile
| Wall
| Open : Nat → Tile
| Start
| Goal

private def parseTiles (l : String) : Option (TwoDArray Tile) :=
  let lines := String.trim <$> l.splitOn "\n"
  if h : lines.isEmpty then
    none
  else do
    let width := String.length $ lines.head (List.isEmpty_eq_false.mp ((Bool.not_eq_true _).mp h))
    let height := lines.length
    -- just convert it all and check validity later. It isn't user input anyhow.
    let mut result : Array Tile := Array.empty
    for line in lines do
      for char in line.toList do
        match char with
        | 'X' => result := result.push Tile.Wall
        | ' ' | '0' => result := result.push (Tile.Open 0)
        | '1' => result := result.push (Tile.Open 1)
        | '2' => result := result.push (Tile.Open 2)
        | '3' => result := result.push (Tile.Open 3)
        | '4' => result := result.push (Tile.Open 4)
        | '5' => result := result.push (Tile.Open 5)
        | '6' => result := result.push (Tile.Open 6)
        | '7' => result := result.push (Tile.Open 7)
        | '8' => result := result.push (Tile.Open 8)
        | '9' => result := result.push (Tile.Open 9)
        | 'g' => result := result.push Tile.Goal
        | 's' => result := result.push Tile.Start
        | _ => throw ()
    if h : result.size = width * height then
      return {
        width,
        height,
        data := result
        valid := h
      }
    else
      throw ()

private inductive WallOrOpen
| Wall
| Open : Nat → WallOrOpen

private structure Labyrinth where
  data : TwoDArray WallOrOpen
  starts : List data.Coordinate
  goals : List data.Coordinate

private def parseLabyrinth (l : String) : Option Labyrinth := do
  let tiles ← parseTiles l
  let tileToWallOrOpen := λ
    | Tile.Start => WallOrOpen.Open 0
    | Tile.Goal => WallOrOpen.Open 0
    | Tile.Open x => WallOrOpen.Open x
    | Tile.Wall => WallOrOpen.Wall
  let data := Functor.map tileToWallOrOpen tiles
  let mut starts : List data.Coordinate := []
  let mut goals : List data.Coordinate := []
  for hr : row in [0:tiles.height] do
    for hc : col in [0:tiles.width] do
      let c : data.Coordinate := { x := ⟨col, hc.upper⟩, y := ⟨row, hr.upper⟩}
      let c2 : tiles.Coordinate := { x := ⟨col, hc.upper⟩, y := ⟨row, hr.upper⟩}
      match tiles[c2] with
      | Tile.Start => starts := c :: starts
      | Tile.Goal => goals := c :: goals
      | _ => continue
  return {data, starts := starts, goals := goals : Labyrinth}

instance {l : Labyrinth} : LeanAStar.AStarNode (l.data.Coordinate) Nat where
  cardinality := l.data.width * l.data.height
  enumerate := TwoDArray.Coordinate.toIndex
  nth := TwoDArray.Coordinate.ofIndex
  nth_inverse_enumerate := funext TwoDArray.Coordinate.ofIndex_inv_toIndex
  enumerate_inverse_nth := funext TwoDArray.Coordinate.toIndex_inv_ofIndex
  costsLe := Nat.ble
  costs_order := ⟨BinaryHeap.nat_ble_to_heap_transitive_le, BinaryHeap.nat_ble_to_heap_le_total⟩
  getNeighbours := λc ↦
    let neighbours : List l.data.Coordinate := if c.x ≠ ⟨0,Nat.pos_of_lt c.x.isLt⟩ then [{c with x := ⟨c.x.val.pred,Nat.lt_of_le_of_lt (Nat.pred_le _) c.x.isLt⟩}] else []
    let neighbours : List l.data.Coordinate := if c.y ≠ ⟨0,Nat.pos_of_lt c.y.isLt⟩ then {c with y := ⟨c.y.val.pred, Nat.lt_of_le_of_lt (Nat.pred_le _) c.y.isLt⟩} :: neighbours else neighbours
    let neighbours : List l.data.Coordinate := if h : c.x.val.succ < l.data.width then {c with x := ⟨c.x.val.succ, h⟩} :: neighbours else neighbours
    let neighbours : List l.data.Coordinate := if h : c.y.val.succ < l.data.height then {c with y := ⟨c.y.val.succ, h⟩} :: neighbours else neighbours
    neighbours.filterMap λc↦ match l.data[c] with
    | .Wall => none
    | .Open x => some (c, x.succ)
  isGoal := l.goals.contains
  remaining_costs_heuristic := λ {x := cx, y := cy} ↦
    let distances : List Nat := l.goals.map λ{x := gx, y := gy} ↦
      let dx : Nat := if gx > cx then gx - cx else cx - gx
      let dy : Nat := if gy > cy then gy - cy else cy - gy
      dx + dy
    Option.getD distances.min? 0

private def Labyrinth.startPoints (l : Labyrinth) : List (LeanAStar.StartPoint (l.data.Coordinate)) :=
  l.starts.map λs ↦
  {
    start := s
    initial_costs := 0
  }

private def labyrinth := "
XXXXXXXXXXXXXX
X XX    XXs  X
X    XX XX X X
XX XXXX X  X X
XX   XX X XX X
XX   XX   XX X
XX XXXXXXXXX X
XX    gX     X
XXXXXXXXXXXXXX
".trim

def testCostsSimple (_ : Unit) : Except String Unit :=
  match parseLabyrinth labyrinth with
    | some l => match LeanAStar.findLowestCosts l.startPoints with
      |some n =>
        if n == 26 then
          Except.ok ()
        else
          Except.error s!"Expected 26, got {n}"
      | none => Except.error "Failed to find a path."
    | none => Except.error "Failed to parse test input. Fix the test."

def testPathSimple (_ : Unit) : Except String Unit :=
  match parseLabyrinth labyrinth with
    | some l => match LeanAStar.findShortestPath l.startPoints with
      |some (n, path) =>
        if n == 26 then
          let path := path.map TwoDArray.Coordinate.toNats
          let expected := [
            (10,1),
            (10,2),
            (10,3),
            (9,3),
            (9,4),
            (9,5),
            (8,5),
            (7,5),
            (7,4),
            (7,3),
            (7,2),
            (7,1),
            (6,1),
            (5,1),
            (4,1),
            (4,2),
            (3,2),
            (2,2),
            (2,3),
            (2,4),
            (2,5),
            (2,6),
            (2,7),
            (3,7),
            (4,7),
            (5,7),
            (6,7)
          ]
          if path == expected then
            Except.ok ()
          else
            Except.error s!"Path did not match expectations. Got: {path}, expected {expected}."
        else
          Except.error s!"Expected costs of 26, got {n}"
      | none => Except.error "Failed to find a path."
    | none => Except.error "Failed to parse test input. Fix the test."

def ListTests : List (String × (Unit → Except String Unit)) :=
  [
    ("testCostsSimple", testCostsSimple),
    ("testPathSimple", testPathSimple)
  ]
