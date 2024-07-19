---
exclude_tags: pandoc
header-args:lean4: ":tangle
  \\~/Desktop/PL-playground/lean4-playground/regex.lean :comments both"
id: 5f03b7c8-9fa5-445d-9fae-624fcf91bc2b
title: [WIP] Derivatives of Regular Expressions
---

Brzozowski\'s derivative is truly a gem in the literature and surprised
me with its beauty when I first learned about it towards the end of
2023, thanks to the reference by Guannan Wei. Derivatives of a language
$r$ with respect to a string $\pi$, in a nutshell, is a new language
containing all strings from the input language when appended to π. One
propertty of derivatives that initially challenged my understanding is
$d_{\pi} r^{\ast} = d_{\pi}r \cdot r^{\ast}$. Through this post, I aim
to sharpen my skills in proof mechanization and learn some Lean by
formalizing my reasoning about this intriguing property.

## Mathlib Import

``` lean
import Mathlib.Data.Prod.Lex
import Mathlib.Order.BooleanAlgebra
import Mathlib.Tactic.Linarith
```

## Some Auxiliary Definitions

``` lean
class Denotation (α : Type) (σ : outParam (Type)) where
  denote : α -> Set σ
```

``` lean
class EffectiveBooleanAlgebra (α : Type) (σ : outParam (Type))
  extends Denotation α σ, Bot α, Top α, HasCompl α, Inf α, Sup α where
  denote_bot : denote ⊥ = ∅
  denote_top : denote ⊤ = univ
  denote_compl : denote (compl a) = univ \ denote a
  denote_inf : denote (a ⊓ b) = denote a ∩ denote b
  denote_sup : denote (a ⊔ b) = denote a ∪ denote b
```

## Regex Definition

``` lean
variable (α : Type) in
inductive Regex where
  | ε : Regex
  | atom : α -> Regex
  | concat : Regex -> Regex -> Regex
  | star : Regex -> Regex
  | neg : Regex -> Regex
  | inter : Regex -> Regex -> Regex
  | union : Regex -> Regex -> Regex
open Regex
```

``` lean
infixr:50 " ⬝ "  => concat
postfix:max "*"  => star
prefix:max "~"   => neg
infixr:40 " ⋒ "  => inter
infixr:35 " ⋓ "  => union
```

## Regex Denotation

``` lean
@[simp]
def star_metric : Regex α -> (ℕ ×ₗ ℕ)
  | ε => (0, 1)
  | atom _ => (0, 1)
  | concat r1 r2 | inter r1 r2 | union r1 r2 =>
    let (h1, n1) := star_metric r1
    let (h2, n2) := star_metric r2
    (max h1 h2, n1 + n2)
  | star r => let (h, n) := star_metric r; (h + 1, n + 1)
  | neg r => let (h, n) := star_metric r; (h, n + 1)

instance : WellFoundedRelation (ℕ ×ₗ ℕ) where
  rel := (· < ·)
  wf  := WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf
```

``` lean
theorem zero_lt_size (r : Regex α) : 0 < (star_metric r).snd :=
  by induction r using Regex.rec with
  | ε | atom _ => simp
  | concat r1 r2 ih1 ih2 | inter r1 r2 ih1 ih2 | union r1 r2 ih1 ih2 =>
    simp; split; rename_i h1 n1 heq1; split; rename_i h2 n2 heq2; simp;
    rewrite [heq1] at ih1; rewrite [heq2] at ih2; simp at ih1 ih2; 
    apply Or.intro_left; assumption
  | star r | neg r => simp; split; simp
```

``` lean
def repeat_cat (R : Regex α) (n : ℕ) : Regex α :=
  match n with
  | 0          => ε
  | Nat.succ n => R ⬝ (repeat_cat R n)

notation f "⁽" n "⁾" => repeat_cat f n
```

``` lean
namespace Regex

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]

def denote (r : Regex α) : Set (List σ) :=
  match r with
  | Regex.ε => ∅
  | Regex.atom ℓ => {[a] | a ∈ Denotation.denote ℓ}
  | Regex.concat r1 r2 => (denote r1) ∪ (denote r2)
  | Regex.star r => {π | ∃ i : ℕ, π ∈ denote (repeat_cat r i)}
  | Regex.neg r => Set.univ \ denote r
  | Regex.inter r1 r2 => denote r1 ∩ denote r2
  | Regex.union r1 r2 => denote r1 ∪ denote r2
termination_by star_metric r
decreasing_by
  all_goals (
    simp only [InvImage, WellFoundedRelation.rel, star_metric]
    try (unfold LT.lt Prod.Lex.instLT max Nat.instMax maxOfLe))
  any_goals (
    split; rename_i h1 n1 heq1; split; rename_i h2 n2 heq2; rw [heq1]; simp
    by_cases h1 < h2 <;> rename_i hineqh
    · apply Prod.Lex.left; split; assumption; linarith
    · by_cases h1 = h2 <;> rename_i heqh <;>
      have pos2 : 0 < (star_metric r2).snd := zero_lt_size r2<;>
      rw [heq2] at pos2<;> simp at pos2
      · rw [heqh]; simp; apply Prod.Lex.right; linarith
      · have disj : h1 = h2 ∨ h2 < h1 := Nat.eq_or_lt_of_not_lt hineqh;
        have : h1 > h2 := (by 
        cases disj with
        | inl h1eqh2 => contradiction
        | inr h2lth1 => linarith);
        split; linarith; apply Prod.Lex.right; linarith)
  any_goals (
    split; rename_i h2 n2 heq2; split; rename_i h1 n1 heq1; rw [heq1]; simp
    by_cases h1 < h2 <;> rename_i hineqh
    · apply Prod.Lex.left; split; linarith; assumption
    · by_cases h1 = h2 <;> rename_i heqh <;>
      have pos1 : 0 < (star_metric r1).snd := zero_lt_size r1<;>
      rw [heq2] at pos1<;> simp at pos1
      · rw [heqh]; simp; apply Prod.Lex.right; linarith
      · have disj : h1 = h2 ∨ h2 < h1 := Nat.eq_or_lt_of_not_lt hineqh;
        have : h1 > h2 := (by 
        cases disj with
        | inl h1eqh2 => contradiction
        | inr h2lth1 => linarith);
        split; apply Prod.Lex.right; linarith; linarith)
  -- repeat (first | (
  --   split; rename_i h1 n1 heq1; split; rename_i h2 n2 heq2; rw [heq1]; simp
  --   by_cases h1 < h2 <;> rename_i hineqh
  --   · apply Prod.Lex.left; split; assumption; linarith
  --   · by_cases h1 = h2 <;> rename_i heqh <;>
  --     have pos2 : 0 < (star_metric r2).snd := zero_lt_size r2<;>
  --     rw [heq2] at pos2<;> simp at pos2
  --     · rw [heqh]; simp; apply Prod.Lex.right; linarith
  --     · have disj : h1 = h2 ∨ h2 < h1 := Nat.eq_or_lt_of_not_lt hineqh;
  --       have : h1 > h2 := (by 
  --         cases disj with
  --         | inl h1eqh2 => contradiction
  --         | inr h2lth1 => linarith);
  --       split; linarith; apply Prod.Lex.right; linarith)
  -- )

end Regex
```

## org → md [[pandoc]{.smallcaps}]{.tag tag-name="pandoc"} {#org-md}

``` {#from-org .elisp}
(buffer-file-name)
```

```{=org}
#+RESULTS: from-org
```
``` example
/home/slark/org-roam/20240128134511-derivatives_of_regular_expressions.org
```

``` {#pwd .elisp export="none"}
(file-name-directory (buffer-file-name))
```

```{=org}
#+RESULTS: pwd
```
``` example
/home/slark/org-roam/
```

``` {#filename .elisp var="full=from-org"}
(file-name-nondirectory full)
```

```{=org}
#+RESULTS: filename
```
``` example
20240128134511-derivatives_of_regular_expressions.org
```

``` {#to-markdown .elisp var="path=from-org dir-for-md=\"~/Desktop/yongweiy.github.io/_posts/\""}
(let* ((current-date (format-time-string "%Y-%m-%d"))
       (new-name (replace-regexp-in-string "^[0-9]+-"
                                           (concat current-date "-")
                                           (file-name-nondirectory path)))
       (md-name (replace-regexp-in-string "\\.org$" ".md" new-name))
       (final-name (concat (expand-file-name dir-for-md) md-name)))
  final-name)
```

```{=org}
#+RESULTS: to-markdown
```
``` example
/home/slark/Desktop/yongweiy.github.io/_posts/2024-07-19-derivatives_of_regular_expressions.md
```

```{=org}
#+RESULTS: to_markdown
```
``` example
~/Desktop/yongweiy.github.io/_posts/2024-07-19-derivatives_of_regular_expressions.md
```

``` {.shell var="from=from-org to=to-markdown" results="silent"}
sed -e 's/#+begin_src lean/#+begin_src lean/g' $from | pandoc -s -f org -o $to
```
