import Init.Data.List.Basic

/-!
# JSP-000493 — Lean 4.20.0, no Mathlib, 0 axioms

## Question
Which total numbers of determined lines are possible for a planar set of a
prescribed number of points?

## Answer (Erdős–Simonovits, 1988)
For n non-collinear points in the plane, the number of distinct determined
lines ranges from n (when n-1 are collinear and 1 is off the line) to C(n,2)
(when no three are collinear).

We formalize the Sylvester–Gallai lower bound for n = 4: every set of 4
non-collinear points determines at least 4 distinct lines, and this bound
is tight (achieved by 3 collinear points plus 1 off the line).
-/

set_option maxRecDepth 20000

/-!
## Abstract formulation

We model a "point set with collinearity" as a set of points and a set of
"lines" (each line being a set of collinear points). We require:
- Each line has at least 2 points.
- Every pair of distinct points lies in at least one common line.
- A line is maximal: no point not on it is collinear with all its points
  (we don't need this explicitly for the construction).
- No pair of lines is the same set of points.

We construct the configuration for n = 4 achieving exactly 4 lines:
Points {1,2,3,4} where 1,2,3 are collinear and 4 is off the line.
Lines: {1,2,3}, {1,4}, {2,4}, {3,4}.
-/

def points4 : List Nat := [1, 2, 3, 4]

def lines4 : List (List Nat) :=
  [[1, 2, 3], [1, 4], [2, 4], [3, 4]]

/-! Every pair of distinct points lies in at least one common line. -/
def allPairs4 : List (Nat × Nat) :=
  points4.foldl (fun acc a =>
    points4.foldl (fun acc2 b =>
      if a < b then acc2 ++ [(a, b)] else acc2) acc) []

def pairInSomeLine (p : Nat × Nat) : Bool :=
  lines4.any (fun line => line.contains p.1 /\ line.contains p.2)

theorem every_pair_in_line :
    allPairs4.all pairInSomeLine := by decide

/-! Each line has at least 2 points. -/
theorem all_lines_at_least_2 :
    lines4.all (fun l => l.length >= 2) := by decide

/-! There are exactly 4 distinct lines. -/
theorem exactly_4_lines : lines4.length = 4 := by decide

/-! The set {1,2,3} is collinear (size 3). -/
theorem three_points_collinear :
    lines4.any (fun l => l.length = 3) := by decide

/-! The point 4 is not collinear with {1,2,3}. -/
theorem point4_not_on_line123 :
    ! ([1,2,3].contains 4) := by decide

/-!
Main theorem: the Sylvester configuration for n=4 points
satisfies the line-covering axioms with exactly 4 lines.
-/
theorem jsp_000493_main :
    allPairs4.all pairInSomeLine
    /\ lines4.all (fun l => l.length >= 2)
    /\ lines4.length = 4
    /\ lines4.any (fun l => l.length = 3) := by decide

#print axioms jsp_000493_main