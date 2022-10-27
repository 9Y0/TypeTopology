Martin Escardo, Paulo Oliva, 27th October 2022

A third version of tic-tac-toe.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

module Games.TicTacToe0 where

open import TypeTopology.CompactTypes
open import TypeTopology.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated

open import MLTT.Spartan hiding (J)
open import MLTT.NonSpartanMLTTTypes hiding (Fin ; 𝟎 ; 𝟏 ; 𝟐 ; 𝟑 ; 𝟒 ; 𝟓 ; 𝟔 ; 𝟕 ; 𝟖 ; 𝟗)
open import MLTT.Fin
open import MLTT.Fin-Properties

R : Type
R = Fin 3

open import Games.TypeTrees
open import Games.FiniteHistoryDependent R

tic-tac-toe₁ : Game
tic-tac-toe₁ = game (tree board₀ 9) (outcome board₀ 9) (quantifiers board₀ 9)
 where
  data Player : Type where
   X O : Player

  opponent : Player → Player
  opponent X = O
  opponent O = X

  pattern X-wins = 𝟎
  pattern draw   = 𝟏
  pattern O-wins = 𝟐

  value : Player → R
  value X = X-wins
  value O = O-wins

  Grid   = R × R
  Matrix = Grid → Maybe Player
  Board  = Player × Matrix

\end{code}

Convention: in a board (p , A), p is the opponent of the the current player.

\begin{code}

  wins : Player → Matrix → Bool
  wins p A = line || col || diag
   where
    _is_ : Maybe Player → Player → Bool
    Nothing is _ = false
    Just X  is X = true
    Just O  is X = false
    Just X  is O = false
    Just O  is O = true

    infix 30 _is_

    l₀ = A (𝟎 , 𝟎) is p && A (𝟎 , 𝟏) is p && A (𝟎 , 𝟐) is p
    l₁ = A (𝟏 , 𝟎) is p && A (𝟏 , 𝟏) is p && A (𝟏 , 𝟐) is p
    l₂ = A (𝟐 , 𝟎) is p && A (𝟐 , 𝟏) is p && A (𝟐 , 𝟐) is p

    c₀ = A (𝟎 , 𝟎) is p && A (𝟏 , 𝟎) is p && A (𝟐 , 𝟎) is p
    c₁ = A (𝟎 , 𝟏) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟏) is p
    c₂ = A (𝟎 , 𝟐) is p && A (𝟏 , 𝟐) is p && A (𝟐 , 𝟐) is p

    d₀ = A (𝟎 , 𝟎) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟐) is p
    d₁ = A (𝟎 , 𝟐) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟎) is p

    line = l₀ || l₁ || l₂
    col  = c₀ || c₁ || c₂
    diag = d₀ || d₁

  Grid-is-discrete : is-discrete Grid
  Grid-is-discrete = ×-is-discrete Fin-is-discrete Fin-is-discrete

  Grid-compact : Compact Grid {𝓤₀}
  Grid-compact = ×-Compact Fin-Compact Fin-Compact

  board₀ : Board
  board₀ = X , (λ _ → Nothing)

  Move : Board → Type
  Move (_ , A) = Σ g ꞉ Grid , A g ＝ Nothing

  Move-decidable : (b : Board) → decidable (Move b)
  Move-decidable (_ , A) = Grid-compact
                            (λ g → A g ＝ Nothing)
                            (λ g → Nothing-is-isolated' (A g))

  Move-compact : (b : Board) → Compact (Move b)
  Move-compact (x , A) = complemented-subset-of-compact-type
                          Grid-compact
                          (λ g → Nothing-is-isolated' (A g))
                          (λ g → Nothing-is-h-isolated' (A g))

  selection : (p : Player) (M : Type) → M → Compact M → J M
  selection X M m κ p = pr₁ (compact-argmax p κ m)
  selection O M m κ p = pr₁ (compact-argmin p κ m)

  update : (p : Player) (A : Matrix)
         → Move (p , A)
         → Matrix
  update p A (m , _) m' = f (Grid-is-discrete m m')
   where
    f : decidable (m ＝ m') → Maybe Player
    f (inl _) = Just p
    f (inr _) = A m'

  play : (b : Board) → Move b → Board
  play (p , A) m = opponent p , update p A m

  tree : Board → ℕ → 𝕋
  tree b         0        = []
  tree b@(p , A) (succ k) = if wins (opponent p) A
                            then []
                            else (Move b ∷ λ m → tree (play b m) k)

  quantifier : Player
             → (M : Type)
             → Compact M
             → decidable M
             → (M → R) → R
  quantifier p M κ (inl m) = overline (selection p M m κ)
  quantifier p M κ (inr _) = λ _ → draw

  outcome : (b : Board) (k : ℕ) → Path (tree b k) → R
  outcome b 0 ⟨⟩ = draw
  outcome b@(p , A) (succ k) xs with wins (opponent p) A
  ... | true  = value (opponent p)
  ... | false = outcome (play b (path-head xs)) k (path-tail xs)

  quantifiers : (b : Board) (k : ℕ) → 𝓚 (tree b k)
  quantifiers b 0 = ⟨⟩
  quantifiers b@(p , A)  (succ k) with wins (opponent p) A
  ... | true  = ⟨⟩
  ... | false = quantifier p (Move b) (Move-compact b) (Move-decidable b)
                :: (λ m → quantifiers (play b m) k)

t₁ : R
t₁ = optimal-outcome tic-tac-toe₁

\end{code}

The above computation takes too long, due to the use of brute-force
search. A more efficient one is in another file.
