import IGSIII4.LongDiamondPaths
import IGSIII4.ForcedPathSupport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII4.LongDiamond

theorem terminal_loop_support (walk : network.fullGraph.Walk (10 : Fin 20) 10)
    (path : walk.IsPath) : walk.support = [10] := by
  cases (SimpleGraph.Walk.isPath_iff_nil.mp path)
  rfl

theorem path_from_9_support (walk : network.fullGraph.Walk (9 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (8 : Fin 20) ∉ walk.support) :
    walk.support = [9, 10] := by
  apply forced_path_step_support (previous := (8 : Fin 20)) (next := (10 : Fin 20))
    (support := [10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 9 vertex →
          vertex = 8 ∨ vertex = 10 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact terminal_loop_support tail tailPath

theorem path_from_8_support (walk : network.fullGraph.Walk (8 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (7 : Fin 20) ∉ walk.support) :
    walk.support = [8, 9, 10] := by
  apply forced_path_step_support (previous := (7 : Fin 20)) (next := (9 : Fin 20))
    (support := [9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 8 vertex →
          vertex = 7 ∨ vertex = 9 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_9_support tail tailPath tailAvoids

theorem path_from_7_support (walk : network.fullGraph.Walk (7 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (6 : Fin 20) ∉ walk.support) :
    walk.support = [7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (6 : Fin 20)) (next := (8 : Fin 20))
    (support := [8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 7 vertex →
          vertex = 6 ∨ vertex = 8 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_8_support tail tailPath tailAvoids

theorem path_from_6_support (walk : network.fullGraph.Walk (6 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (5 : Fin 20) ∉ walk.support) :
    walk.support = [6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (5 : Fin 20)) (next := (7 : Fin 20))
    (support := [7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 6 vertex →
          vertex = 5 ∨ vertex = 7 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_7_support tail tailPath tailAvoids

theorem path_from_5_support (walk : network.fullGraph.Walk (5 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (4 : Fin 20) ∉ walk.support) :
    walk.support = [5, 6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (4 : Fin 20)) (next := (6 : Fin 20))
    (support := [6, 7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 5 vertex →
          vertex = 4 ∨ vertex = 6 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_6_support tail tailPath tailAvoids

theorem path_from_4_support (walk : network.fullGraph.Walk (4 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (3 : Fin 20) ∉ walk.support) :
    walk.support = [4, 5, 6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (3 : Fin 20)) (next := (5 : Fin 20))
    (support := [5, 6, 7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 4 vertex →
          vertex = 3 ∨ vertex = 5 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_5_support tail tailPath tailAvoids

theorem path_from_3_support (walk : network.fullGraph.Walk (3 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (2 : Fin 20) ∉ walk.support) :
    walk.support = [3, 4, 5, 6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (2 : Fin 20)) (next := (4 : Fin 20))
    (support := [4, 5, 6, 7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 3 vertex →
          vertex = 2 ∨ vertex = 4 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_4_support tail tailPath tailAvoids

theorem path_from_2_support (walk : network.fullGraph.Walk (2 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (1 : Fin 20) ∉ walk.support) :
    walk.support = [2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (1 : Fin 20)) (next := (3 : Fin 20))
    (support := [3, 4, 5, 6, 7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 2 vertex →
          vertex = 1 ∨ vertex = 3 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_3_support tail tailPath tailAvoids

theorem path_from_1_support (walk : network.fullGraph.Walk (1 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (0 : Fin 20) ∉ walk.support) :
    walk.support = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := by
  apply forced_path_step_support (previous := (0 : Fin 20)) (next := (2 : Fin 20))
    (support := [2, 3, 4, 5, 6, 7, 8, 9, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 1 vertex →
          vertex = 0 ∨ vertex = 2 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_2_support tail tailPath tailAvoids

theorem path_from_11_support (walk : network.fullGraph.Walk (11 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (12 : Fin 20) ∉ walk.support) :
    walk.support = [11, 10] := by
  apply forced_path_step_support (previous := (12 : Fin 20)) (next := (10 : Fin 20))
    (support := [10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 11 vertex →
          vertex = 12 ∨ vertex = 10 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact terminal_loop_support tail tailPath

theorem path_from_12_support (walk : network.fullGraph.Walk (12 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (13 : Fin 20) ∉ walk.support) :
    walk.support = [12, 11, 10] := by
  apply forced_path_step_support (previous := (13 : Fin 20)) (next := (11 : Fin 20))
    (support := [11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 12 vertex →
          vertex = 13 ∨ vertex = 11 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_11_support tail tailPath tailAvoids

theorem path_from_13_support (walk : network.fullGraph.Walk (13 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (14 : Fin 20) ∉ walk.support) :
    walk.support = [13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (14 : Fin 20)) (next := (12 : Fin 20))
    (support := [12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 13 vertex →
          vertex = 14 ∨ vertex = 12 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_12_support tail tailPath tailAvoids

theorem path_from_14_support (walk : network.fullGraph.Walk (14 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (15 : Fin 20) ∉ walk.support) :
    walk.support = [14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (15 : Fin 20)) (next := (13 : Fin 20))
    (support := [13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 14 vertex →
          vertex = 15 ∨ vertex = 13 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_13_support tail tailPath tailAvoids

theorem path_from_15_support (walk : network.fullGraph.Walk (15 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (16 : Fin 20) ∉ walk.support) :
    walk.support = [15, 14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (16 : Fin 20)) (next := (14 : Fin 20))
    (support := [14, 13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 15 vertex →
          vertex = 16 ∨ vertex = 14 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_14_support tail tailPath tailAvoids

theorem path_from_16_support (walk : network.fullGraph.Walk (16 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (17 : Fin 20) ∉ walk.support) :
    walk.support = [16, 15, 14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (17 : Fin 20)) (next := (15 : Fin 20))
    (support := [15, 14, 13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 16 vertex →
          vertex = 17 ∨ vertex = 15 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_15_support tail tailPath tailAvoids

theorem path_from_17_support (walk : network.fullGraph.Walk (17 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (18 : Fin 20) ∉ walk.support) :
    walk.support = [17, 16, 15, 14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (18 : Fin 20)) (next := (16 : Fin 20))
    (support := [16, 15, 14, 13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 17 vertex →
          vertex = 18 ∨ vertex = 16 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_16_support tail tailPath tailAvoids

theorem path_from_18_support (walk : network.fullGraph.Walk (18 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (19 : Fin 20) ∉ walk.support) :
    walk.support = [18, 17, 16, 15, 14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (19 : Fin 20)) (next := (17 : Fin 20))
    (support := [17, 16, 15, 14, 13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 18 vertex →
          vertex = 19 ∨ vertex = 17 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_17_support tail tailPath tailAvoids

theorem path_from_19_support (walk : network.fullGraph.Walk (19 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (0 : Fin 20) ∉ walk.support) :
    walk.support = [19, 18, 17, 16, 15, 14, 13, 12, 11, 10] := by
  apply forced_path_step_support (previous := (0 : Fin 20)) (next := (18 : Fin 20))
    (support := [18, 17, 16, 15, 14, 13, 12, 11, 10]) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 19 vertex →
          vertex = 0 ∨ vertex = 18 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_18_support tail tailPath tailAvoids

theorem exactly_two_terminal_paths (walk : network.fullGraph.Walk network.source network.target)
    (path : walk.IsPath) : walk = lowerWalk ∨ walk = upperWalk := by
  have supports : walk.support = lowerWalk.support ∨ walk.support = upperWalk.support := by
    change network.fullGraph.Walk (0 : Fin 20) 10 at walk
    cases walk with
    | @cons start neighbor terminal adjacent tail =>
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 0 vertex →
          vertex = 1 ∨ vertex = 19 := by decide
      rcases neighbors neighbor adjacent with rfl | rfl
      · left
        change (0 : Fin 20) :: tail.support = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
        rw [path_from_1_support tail path.of_cons
          (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]
      · right
        change (0 : Fin 20) :: tail.support = [0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10]
        rw [path_from_19_support tail path.of_cons
          (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]
  exact supports.imp SimpleGraph.Walk.ext_support SimpleGraph.Walk.ext_support

theorem two_terminal_paths_distinct : lowerWalk ≠ upperWalk := by
  intro equality
  have supportEquality := congrArg SimpleGraph.Walk.support equality
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)) =
    [0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] at supportEquality
  have different : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)) ≠
    [0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] := by decide
  exact different supportEquality

end IGSIII4.LongDiamond
