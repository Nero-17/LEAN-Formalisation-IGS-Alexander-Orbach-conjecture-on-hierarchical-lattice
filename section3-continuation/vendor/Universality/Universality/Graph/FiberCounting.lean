import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace Universality

theorem card_images_eq_of_fibers {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (domain : Finset α) (first : α → β) (second : α → γ)
    (hfibers : ∀ a ∈ domain, ∀ b ∈ domain, first a = first b ↔ second a = second b) :
    (domain.image first).card = (domain.image second).card := by
  classical
  have hchoice (value : β) (hvalue : value ∈ domain.image first) :
      ∃ a, a ∈ domain ∧ first a = value := Finset.mem_image.mp hvalue
  apply Finset.card_bij (fun value hvalue => second (Classical.choose (hchoice value hvalue)))
  · intro value hvalue
    exact Finset.mem_image.mpr ⟨_, (Classical.choose_spec (hchoice value hvalue)).1, rfl⟩
  · intro firstValue hfirst secondValue hsecond heq
    have h := (hfibers _ (Classical.choose_spec (hchoice firstValue hfirst)).1
      _ (Classical.choose_spec (hchoice secondValue hsecond)).1).mpr heq
    simpa only [(Classical.choose_spec (hchoice firstValue hfirst)).2,
      (Classical.choose_spec (hchoice secondValue hsecond)).2] using h
  · intro value hvalue
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hvalue
    have himage : first a ∈ domain.image first := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    refine ⟨first a, himage, ?_⟩
    exact (hfibers _ (Classical.choose_spec (hchoice (first a) himage)).1 a ha).mp
      (Classical.choose_spec (hchoice (first a) himage)).2

end Universality
