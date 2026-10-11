import IGSIII4.LongDiamondBase
import IGSIII4.ForcedPathStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII4.LongDiamond

theorem terminal_loop_length (walk : network.fullGraph.Walk (10 : Fin 20) 10)
    (path : walk.IsPath) : walk.length = 0 := by
  cases (SimpleGraph.Walk.isPath_iff_nil.mp path)
  rfl

theorem path_from_9_length (walk : network.fullGraph.Walk (9 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (8 : Fin 20) ∉ walk.support) : walk.length = 1 := by
  apply forced_path_step (previous := (8 : Fin 20)) (next := (10 : Fin 20))
    (length := 0) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 9 vertex →
          vertex = 8 ∨ vertex = 10 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact terminal_loop_length tail tailPath

theorem path_from_8_length (walk : network.fullGraph.Walk (8 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (7 : Fin 20) ∉ walk.support) : walk.length = 2 := by
  apply forced_path_step (previous := (7 : Fin 20)) (next := (9 : Fin 20))
    (length := 1) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 8 vertex →
          vertex = 7 ∨ vertex = 9 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_9_length tail tailPath tailAvoids

theorem path_from_7_length (walk : network.fullGraph.Walk (7 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (6 : Fin 20) ∉ walk.support) : walk.length = 3 := by
  apply forced_path_step (previous := (6 : Fin 20)) (next := (8 : Fin 20))
    (length := 2) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 7 vertex →
          vertex = 6 ∨ vertex = 8 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_8_length tail tailPath tailAvoids

theorem path_from_6_length (walk : network.fullGraph.Walk (6 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (5 : Fin 20) ∉ walk.support) : walk.length = 4 := by
  apply forced_path_step (previous := (5 : Fin 20)) (next := (7 : Fin 20))
    (length := 3) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 6 vertex →
          vertex = 5 ∨ vertex = 7 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_7_length tail tailPath tailAvoids

theorem path_from_5_length (walk : network.fullGraph.Walk (5 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (4 : Fin 20) ∉ walk.support) : walk.length = 5 := by
  apply forced_path_step (previous := (4 : Fin 20)) (next := (6 : Fin 20))
    (length := 4) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 5 vertex →
          vertex = 4 ∨ vertex = 6 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_6_length tail tailPath tailAvoids

theorem path_from_4_length (walk : network.fullGraph.Walk (4 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (3 : Fin 20) ∉ walk.support) : walk.length = 6 := by
  apply forced_path_step (previous := (3 : Fin 20)) (next := (5 : Fin 20))
    (length := 5) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 4 vertex →
          vertex = 3 ∨ vertex = 5 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_5_length tail tailPath tailAvoids

theorem path_from_3_length (walk : network.fullGraph.Walk (3 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (2 : Fin 20) ∉ walk.support) : walk.length = 7 := by
  apply forced_path_step (previous := (2 : Fin 20)) (next := (4 : Fin 20))
    (length := 6) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 3 vertex →
          vertex = 2 ∨ vertex = 4 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_4_length tail tailPath tailAvoids

theorem path_from_2_length (walk : network.fullGraph.Walk (2 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (1 : Fin 20) ∉ walk.support) : walk.length = 8 := by
  apply forced_path_step (previous := (1 : Fin 20)) (next := (3 : Fin 20))
    (length := 7) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 2 vertex →
          vertex = 1 ∨ vertex = 3 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_3_length tail tailPath tailAvoids

theorem path_from_1_length (walk : network.fullGraph.Walk (1 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (0 : Fin 20) ∉ walk.support) : walk.length = 9 := by
  apply forced_path_step (previous := (0 : Fin 20)) (next := (2 : Fin 20))
    (length := 8) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 1 vertex →
          vertex = 0 ∨ vertex = 2 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_2_length tail tailPath tailAvoids

theorem path_from_11_length (walk : network.fullGraph.Walk (11 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (12 : Fin 20) ∉ walk.support) : walk.length = 1 := by
  apply forced_path_step (previous := (12 : Fin 20)) (next := (10 : Fin 20))
    (length := 0) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 11 vertex →
          vertex = 12 ∨ vertex = 10 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact terminal_loop_length tail tailPath

theorem path_from_12_length (walk : network.fullGraph.Walk (12 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (13 : Fin 20) ∉ walk.support) : walk.length = 2 := by
  apply forced_path_step (previous := (13 : Fin 20)) (next := (11 : Fin 20))
    (length := 1) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 12 vertex →
          vertex = 13 ∨ vertex = 11 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_11_length tail tailPath tailAvoids

theorem path_from_13_length (walk : network.fullGraph.Walk (13 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (14 : Fin 20) ∉ walk.support) : walk.length = 3 := by
  apply forced_path_step (previous := (14 : Fin 20)) (next := (12 : Fin 20))
    (length := 2) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 13 vertex →
          vertex = 14 ∨ vertex = 12 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_12_length tail tailPath tailAvoids

theorem path_from_14_length (walk : network.fullGraph.Walk (14 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (15 : Fin 20) ∉ walk.support) : walk.length = 4 := by
  apply forced_path_step (previous := (15 : Fin 20)) (next := (13 : Fin 20))
    (length := 3) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 14 vertex →
          vertex = 15 ∨ vertex = 13 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_13_length tail tailPath tailAvoids

theorem path_from_15_length (walk : network.fullGraph.Walk (15 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (16 : Fin 20) ∉ walk.support) : walk.length = 5 := by
  apply forced_path_step (previous := (16 : Fin 20)) (next := (14 : Fin 20))
    (length := 4) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 15 vertex →
          vertex = 16 ∨ vertex = 14 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_14_length tail tailPath tailAvoids

theorem path_from_16_length (walk : network.fullGraph.Walk (16 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (17 : Fin 20) ∉ walk.support) : walk.length = 6 := by
  apply forced_path_step (previous := (17 : Fin 20)) (next := (15 : Fin 20))
    (length := 5) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 16 vertex →
          vertex = 17 ∨ vertex = 15 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_15_length tail tailPath tailAvoids

theorem path_from_17_length (walk : network.fullGraph.Walk (17 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (18 : Fin 20) ∉ walk.support) : walk.length = 7 := by
  apply forced_path_step (previous := (18 : Fin 20)) (next := (16 : Fin 20))
    (length := 6) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 17 vertex →
          vertex = 18 ∨ vertex = 16 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_16_length tail tailPath tailAvoids

theorem path_from_18_length (walk : network.fullGraph.Walk (18 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (19 : Fin 20) ∉ walk.support) : walk.length = 8 := by
  apply forced_path_step (previous := (19 : Fin 20)) (next := (17 : Fin 20))
    (length := 7) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 18 vertex →
          vertex = 19 ∨ vertex = 17 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_17_length tail tailPath tailAvoids

theorem path_from_19_length (walk : network.fullGraph.Walk (19 : Fin 20) 10)
    (path : walk.IsPath) (avoids : (0 : Fin 20) ∉ walk.support) : walk.length = 9 := by
  apply forced_path_step (previous := (0 : Fin 20)) (next := (18 : Fin 20))
    (length := 8) (by decide) (by
      have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 19 vertex →
          vertex = 0 ∨ vertex = 18 := by decide
      exact neighbors) ?_ walk path avoids
  intro tail tailPath tailAvoids
  exact path_from_18_length tail tailPath tailAvoids

theorem equal_terminal_path_lengths (walk : network.fullGraph.Walk network.source network.target)
    (path : walk.IsPath) : walk.length = 10 := by
  change network.fullGraph.Walk (0 : Fin 20) 10 at walk
  cases walk with
  | @cons start neighbor terminal adjacent tail =>
    have neighbors : ∀ vertex : Fin 20, network.fullGraph.Adj 0 vertex →
        vertex = 1 ∨ vertex = 19 := by decide
    rcases neighbors neighbor adjacent with rfl | rfl
    · rw [SimpleGraph.Walk.length_cons, path_from_1_length tail path.of_cons
        (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]
    · rw [SimpleGraph.Walk.length_cons, path_from_19_length tail path.of_cons
        (SimpleGraph.Walk.cons_isPath_iff adjacent tail |>.mp path).2]

end IGSIII4.LongDiamond
