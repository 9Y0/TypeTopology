Tom de Jong, 1 March 2021

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-Base

open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons

module CircleInduction where

𝓛 : (X : 𝓤 ̇ ) → 𝓤 ̇
𝓛 X = Σ x ꞉ X , x ≡ x

𝓛-functor : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → 𝓛 X → 𝓛 Y
𝓛-functor f (x , p) = f x , ap f p

𝓛-functor-id : {X : 𝓤 ̇ } → 𝓛-functor id ∼ id {𝓤} {𝓛 X}
𝓛-functor-id {𝓤} {X} (x , p) = to-Σ-≡ (refl , γ p)
 where
  γ : {y z : X} (q : y ≡ z) → transport (λ - → y ≡ -) q refl ≡ q
  γ refl = refl

𝓛-functor-comp : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } (f : X → Y) (g : Y → Z)
               → 𝓛-functor g ∘ 𝓛-functor f ∼ 𝓛-functor (g ∘ f)
𝓛-functor-comp f g (x , p) = to-Σ-≡ (refl , (ap-ap f g p))

𝓛-functor-dep : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (f : (x : X) → Y x) → 𝓛 X → 𝓛 (Σ Y)
𝓛-functor-dep f (x , p) = (x , f x) , to-Σ-≡ (p , (apd f p))

module _
        (𝕊¹ : 𝓤 ̇ )
        (base : 𝕊¹)
        (loop : base ≡ base)
       where

 𝕊¹-universal-map : (A : 𝓥 ̇ )
                  → (𝕊¹ → A) → 𝓛 A
 𝕊¹-universal-map A f = (f base) , (ap f loop)

 module _
         (𝕊¹-universal-property : {𝓥 : Universe} (A : 𝓥 ̇ )
                                → is-equiv (𝕊¹-universal-map A))
        where

  𝕊¹-uniqueness-principle : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                          → ∃! r ꞉ (𝕊¹ → A) , (r base , ap r loop) ≡ (a , p)
  𝕊¹-uniqueness-principle {𝓥} {A} a p =
    equivs-are-vv-equivs (𝕊¹-universal-map A)
                         (𝕊¹-universal-property A) (a , p)

  𝕊¹-rec : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
         → 𝕊¹ → A
  𝕊¹-rec {𝓥} {A} a p = (∃!-witness (𝕊¹-uniqueness-principle a p))

  𝕊¹-rec-comp : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
              → (𝕊¹-rec a p base , ap (𝕊¹-rec a p) loop) ≡[ 𝓛 A ] (a , p)
  𝕊¹-rec-comp {𝓥} {A} a p = ∃!-is-witness (𝕊¹-uniqueness-principle a p)

  𝕊¹-rec-on-base : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                 → 𝕊¹-rec a p base ≡ a
  𝕊¹-rec-on-base a p = pr₁ (from-Σ-≡ (𝕊¹-rec-comp a p))

  𝕊¹-rec-on-loop : {A : 𝓥 ̇ } (a : A) (p : a ≡ a)
                 → transport (λ - → - ≡ -) (𝕊¹-rec-on-base a p)
                    (ap (𝕊¹-rec a p) loop)
                 ≡ p
  𝕊¹-rec-on-loop a p = pr₂ (from-Σ-≡ (𝕊¹-rec-comp a p))

  coherence : {A : 𝓥 ̇ } (a : A) (p : a ≡ a) (f g : 𝕊¹ → A)
              (u : 𝓛-functor f (base , loop) ≡ (a , p))
              (v : 𝓛-functor g (base , loop) ≡ (a , p))
            → ap (λ - → 𝓛-functor - (base , loop))
               (ap pr₁ (singletons-are-props
                        (𝕊¹-uniqueness-principle a p) (f , u) (g , v)))
            ≡ u ∙ v ⁻¹
  coherence {𝓥} {A} a p f g refl v = γ
   where
    υ : (f , refl) ≡ (g , v)
    υ = singletons-are-props (𝕊¹-uniqueness-principle a p) (f , refl) (g , v)
    υ₁ : f ≡ g
    υ₁ = ap pr₁ υ
    υ₂ : transport
          (λ - → 𝓛-functor (pr₁ -) (base , loop) ≡ 𝓛-functor f (base , loop))
          υ refl
       ≡ v
    υ₂ = apd pr₂ υ
    γ : ap (λ - → 𝓛-functor - (base , loop))
          (ap pr₁
           (singletons-are-props
            (𝕊¹-uniqueness-principle (f base) (ap f loop)) (f , refl) (g , v)))
          ≡ refl ∙ v ⁻¹
    γ = ap (λ - → 𝓛-functor - (base , loop))
          (ap pr₁
           (singletons-are-props
            (𝕊¹-uniqueness-principle (f base) (ap f loop)) (f , refl) (g , v))) ≡⟨ ap-ap pr₁ (λ - → 𝓛-functor - (base , loop)) υ ⟩
        ap (λ - → 𝓛-functor (pr₁ -) (base , loop)) υ ≡⟨ refl ⟩
        transport (λ - → 𝓛-functor f (base , loop) ≡ 𝓛-functor (pr₁ -) (base , loop)) υ refl ≡⟨ ψ f g refl v υ ⟩
        (transport
          (λ - → 𝓛-functor (pr₁ -) (base , loop) ≡ 𝓛-functor f (base , loop))
          υ refl) ⁻¹ ≡⟨ ap _⁻¹ υ₂ ⟩
        v ⁻¹ ≡⟨ refl-left-neutral ⁻¹ ⟩
        refl ∙ v ⁻¹ ∎
     where
      ψ : (f g : 𝕊¹ → A) (u : 𝓛-functor f (base , loop) ≡ (a , p))
          (v : 𝓛-functor g (base , loop) ≡ (a , p))
          (ω : (f , u) ≡ (g , v))
        → transport (λ - → 𝓛-functor f (base , loop) ≡ 𝓛-functor (pr₁ -) (base , loop)) ω refl
        ≡ (transport (λ - → 𝓛-functor (pr₁ -) (base , loop) ≡ 𝓛-functor f (base , loop)) ω refl) ⁻¹
      ψ f g u v refl = refl

--   module 𝕊¹-induction
--           (A : 𝕊¹ → 𝓥 ̇ )
--           (a : A base)
--           (l : transport A loop a ≡ a)
--           (fe : funext 𝓤 (𝓤 ⊔ 𝓥))
--          where

--    -- (base , a) : Σ A

--    l⁺ : (base , a) ≡[ Σ A ] (base , a)
--    l⁺ = to-Σ-≡ (loop , l)

--    r : 𝕊¹ → Σ A
--    r = 𝕊¹-rec (base , a) l⁺

--    -- pr₁ ∘ r : 𝕊¹ → Σ A → 𝕊¹ is this id?

--    𝕊¹-induction-key-≡ : ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop)
--                       ≡[ 𝓛 𝕊¹ ] (base , loop)
--    𝕊¹-induction-key-≡ =
--     ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop) ≡⟨ I    ⟩
--     (pr₁ (r base) , ap pr₁ (ap r loop))  ≡⟨ refl ⟩
--     𝓛-functor pr₁ (r base , ap r loop)   ≡⟨ II   ⟩
--     𝓛-functor pr₁ ((base , a) , l⁺)      ≡⟨ refl ⟩
--     (base , ap pr₁ l⁺)                   ≡⟨ refl ⟩
--     (base , ap pr₁ (to-Σ-≡ (loop , l)))  ≡⟨ III  ⟩
--     (base , loop)                        ∎
--      where
--       I   = ap (λ - → ((pr₁ ∘ r) base , -)) ((ap-ap r pr₁ loop) ⁻¹)
--       II  = ap (𝓛-functor pr₁) (𝕊¹-rec-comp (base , a) l⁺)
--       III = ap (λ - → (base , -)) (ap-pr₁-to-Σ-≡ (loop , l))

--    𝕊¹-induction-key-lemma : pr₁ ∘ r ≡ id
--    𝕊¹-induction-key-lemma =
--     pr₁ (from-Σ-≡ (singletons-are-props (𝕊¹-uniqueness-principle base loop)
--              (pr₁ ∘ r , 𝕊¹-induction-key-≡              )
--              (id      , to-Σ-≡ (refl , ap-id-is-id loop))))

--    𝕊¹-induction : (x : 𝕊¹) → A x
--    𝕊¹-induction x = transport A (happly 𝕊¹-induction-key-lemma x) (pr₂ (r x))
--    -- pr₂ (r x) : A (pr₁ (r x))
--    --                  ||
--    -- transport ... : A(x)

--    𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
--                      ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
--    𝕊¹-induction-comp = {!!}

--    ρ : 𝕊¹ → Σ A
--    ρ x = (x , 𝕊¹-induction x)

--    lemma₁ : (r base , ap r loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
--    lemma₁ = 𝕊¹-rec-comp (base , a) l⁺

--    lemma₂ : ρ ∼ r
--    lemma₂ x = to-Σ-≡ ((γ₁ ⁻¹) , γ₂)
--     where
--      γ₁ : pr₁ (r x) ≡ pr₁ (ρ x)
--      γ₁ = happly 𝕊¹-induction-key-lemma x
--      γ₂ = transport A (γ₁ ⁻¹) (pr₂ (ρ x))                  ≡⟨ refl ⟩
--           transport A (γ₁ ⁻¹) (transport A γ₁ (pr₂ (r x))) ≡⟨ I    ⟩
--           transport A (γ₁ ∙ γ₁ ⁻¹) (pr₂ (r x))             ≡⟨ II   ⟩
--           transport A refl (pr₂ (r x))                     ≡⟨ refl ⟩
--           pr₂ (r x)                                        ∎
--       where
--        I  = (transport-comp A γ₁ (γ₁ ⁻¹)) ⁻¹
--        II = ap (λ - → transport A - (pr₂ (r x))) ((right-inverse γ₁) ⁻¹)

--    transport-along-≡-dup : {X : 𝓦 ̇ } {x y : X} (q : x ≡ y) (p : x ≡ x)
--                          → transport (λ - → - ≡ -) q p ≡ q ⁻¹ ∙ p ∙ q
--    transport-along-≡-dup refl p = p                  ≡⟨ refl-left-neutral ⁻¹ ⟩
--                                   refl ∙ p           ≡⟨ refl                 ⟩
--                                   refl ⁻¹ ∙ p ∙ refl ∎

--    lemma₃ : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] (r base , ap r loop)
--    lemma₃ = to-Σ-≡ (lemma₂ base , γ)
--     where
--      γ = transport (λ - → - ≡ -) (lemma₂ base) (ap ρ loop) ≡⟨ I  ⟩
--          lemma₂ base ⁻¹ ∙ ap ρ loop ∙ lemma₂ base          ≡⟨ II ⟩
--          ap r loop ∎
--       where
--        I  = transport-along-≡-dup (lemma₂ base) (ap ρ loop)
--        II = homotopies-are-natural'' ρ r lemma₂ {base} {base} {loop}

--    lemma₂' : ρ ≡ r
--    lemma₂' = dfunext fe lemma₂

--    lemma₃' : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] (r base , ap r loop)
--    lemma₃' = happly (ap 𝓛-functor lemma₂') (base , loop)

--    {-
--    this : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] ((base , a) , to-Σ-≡ (loop , l))
--    this = lemma₃ ∙ lemma₁

--     𝓛-functor ρ (base , loop)

--    that : ((base , 𝕊¹-induction base) , ap ρ loop) ≡[ 𝓛 (Σ A) ] ((base , a) , to-Σ-≡ (loop , l))
--    that = lemma₃' ∙ lemma₁
--    -}

--    this' : (ρ base) ≡[ Σ A ] (base , a)
--    this' = lemma₂ base ∙ 𝕊¹-rec-on-base (base , a) l⁺

--    what-we-would-like : pr₁ (from-Σ-≡ (𝕊¹-rec-on-base (base , a) l⁺))
--                       ≡ happly 𝕊¹-induction-key-lemma base
--    what-we-would-like = {!abstract-nonsense!}

--    this-would-give : pr₁ (from-Σ-≡ this') ≡ refl
--    this-would-give =
--     pr₁ (from-Σ-≡ this') ≡⟨ refl ⟩
--     pr₁ (from-Σ-≡ (lemma₂ base ∙ 𝕊¹-rec-on-base (base , a) l⁺)) ≡⟨ {!!} ⟩
--     pr₁ (from-Σ-≡ (lemma₂ base)) ∙ pr₁ (from-Σ-≡ (𝕊¹-rec-on-base (base , a) l⁺)) ≡⟨ {!!} ⟩
--     pr₁ (from-Σ-≡ (lemma₂ base)) ∙ (happly 𝕊¹-induction-key-lemma base) ≡⟨ IV ⟩
--     (happly 𝕊¹-induction-key-lemma base) ⁻¹ ∙ (happly 𝕊¹-induction-key-lemma base) ≡⟨ {!!} ⟩
--     refl ∎
--      where
--       IV = ap (λ - → - ∙ happly 𝕊¹-induction-key-lemma base) γ
--        where
--         γ : pr₁ (from-Σ-≡ (lemma₂ base))
--           ≡ happly 𝕊¹-induction-key-lemma base ⁻¹
--         γ = ap pr₁ (fromto-Σ-≡ ((γ₁ ⁻¹) , γ₂))
--          where
--           γ₁ : pr₁ (r base) ≡ pr₁ (ρ base)
--           γ₁ = happly 𝕊¹-induction-key-lemma base
--           γ₂ = transport A (γ₁ ⁻¹) (pr₂ (ρ base))                  ≡⟨ refl ⟩
--                transport A (γ₁ ⁻¹) (transport A γ₁ (pr₂ (r base))) ≡⟨ I    ⟩
--                transport A (γ₁ ∙ γ₁ ⁻¹) (pr₂ (r base))             ≡⟨ II   ⟩
--                transport A refl (pr₂ (r base))                     ≡⟨ refl ⟩
--                pr₂ (r base)                                        ∎
--            where
--             I  = (transport-comp A γ₁ (γ₁ ⁻¹)) ⁻¹
--             II = ap (λ - → transport A - (pr₂ (r base))) ((right-inverse γ₁) ⁻¹)

--    abstract-nonsense : (X : 𝓦 ̇ ) (Y : X → 𝓦' ̇ )
--                        (x : X) (y y' : Y x)
--                        (w : (x , y) ≡[ Σ Y ] (x , y'))
--                      → pr₁ (from-Σ-≡ w) ≡ refl
--                      → y ≡ y'
--    abstract-nonsense X Y x y y' w p = γ (pr₁ (from-Σ-≡ w)) p ∙ pr₂ (from-Σ-≡ w)
--     where
--      γ : (r : x ≡ x) → (r ≡ refl) → y ≡ transport Y r y
--      γ r₁ refl = refl

--    this-does-help : 𝕊¹-induction base ≡ a
--    this-does-help = abstract-nonsense 𝕊¹ A (pr₁ (ρ base)) (𝕊¹-induction base) a
--                      this' this-would-give

--    {-
--    this-would-give : ap (pr₁ ∘ pr₁) this ≡ refl
--    this-would-give = {!!}
--    -}

-- --    abstract-nonsense : (X : 𝓦 ̇ ) (Y : X → 𝓦' ̇ )
-- --                      → (σ τ : Σ Y)
-- --                      → ap (pr₁) σ ≡ refl
-- --                      → ap (pr₁) τ ≡ refl
-- --    abstract-nonsense = ?



-- -- --  --TO DO: DUPLICATION



-- -- -- --    r-on-base : r base ≡ (base , a)
-- -- -- --    r-on-base = 𝕊¹-rec-on-base (base , a) l⁺

-- -- -- --    r-on-base₁ : pr₁ (r base) ≡ base
-- -- -- --    r-on-base₁ = pr₁ (from-Σ-≡ r-on-base)

-- -- -- --    r-on-base₂ : transport A r-on-base₁ (pr₂ (r base)) ≡ a
-- -- -- --    r-on-base₂ = pr₂ (from-Σ-≡ r-on-base)

-- -- -- --    𝕊¹-induction-on-base : 𝕊¹-induction base ≡ a
-- -- -- --    𝕊¹-induction-on-base =
-- -- -- --     𝕊¹-induction base ≡⟨ refl ⟩
-- -- -- --     transport A (happly 𝕊¹-induction-key-lemma base) (pr₂ (r base)) ≡⟨ γ ⟩
-- -- -- --     {!!} ≡⟨ {!!} ⟩
-- -- -- --     transport A r-on-base₁ (pr₂ (r base)) ≡⟨ r-on-base₂ ⟩
-- -- -- --     a ∎
-- -- -- --      where
-- -- -- --       γ = {!!}

-- -- -- --    r-on-loop : transport (λ - → - ≡ -) r-on-base (ap r loop) ≡ l⁺
-- -- -- --    r-on-loop = 𝕊¹-rec-on-loop (base , a) l⁺

-- -- -- --    r-on-loop₁ : pr₁ (from-Σ-≡ (transport (λ - → - ≡ -) r-on-base (ap r loop)))
-- -- -- --               ≡ loop
-- -- -- --    r-on-loop₁ = ap (pr₁ ∘ from-Σ-≡) r-on-loop ∙ ap pr₁ (fromto-Σ-≡ (loop , l))

-- -- -- --    r-on-loop₂ : transport (λ z → transport A (pr₁ (from-Σ-≡ z)) a ≡ a) r-on-loop
-- -- -- --                   (pr₂ (from-Σ-≡ (transport (λ - → - ≡ -) r-on-base (ap r loop))))
-- -- -- --                   ≡ pr₂ (from-Σ-≡ l⁺)
-- -- -- --    r-on-loop₂ = apd (pr₂ ∘ from-Σ-≡) r-on-loop ∙ {!!}



-- -- -- -- {-
-- -- -- -- η : {X : 𝓤 ̇ } → X → 𝓛 X
-- -- -- -- η x = (x , refl)

-- -- -- -- ♯ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → 𝓛 Y) → 𝓛 X → 𝓛 Y
-- -- -- -- ♯ {𝓤} {𝓥} {X} {Y} f (x , p) = y , {!!}
-- -- -- --  where
-- -- -- --   y : Y
-- -- -- --   y = pr₁ (f x)
-- -- -- --   q : y ≡ y
-- -- -- --   q = pr₂ (f x)
-- -- -- --   r : y ≡ y
-- -- -- --   r = ap (pr₁ ∘ f) p
-- -- -- -- -}

-- -- -- -- --    ccc : {!!} -- pr₂ (from-Σ-≡ l⁺) ≡ l
-- -- -- -- --    ccc = {!!}

-- -- -- -- --    exp : {X : 𝓦 ̇ } {Y : X → 𝓦' ̇ } (x₀ x₁ x₂ : X) (y₁ : Y x₁) (y₂ : Y x₂)
-- -- -- -- --          (p₀ : x₀ ≡ x₀) (p₁ : x₁ ≡ x₁) (p₂ : x₂ ≡ x₂)
-- -- -- -- --          (q₁ : transport Y p₁ y₁ ≡ y₁) (q₂ : transport Y p₂ y₂ ≡ y₂)
-- -- -- -- --          (r₁ : 𝓛-functor pr₁ ((x₁ , y₁) , to-Σ-≡ (p₁ , q₁)) ≡[ 𝓛 X ] (x₀ , p₀))
-- -- -- -- --          (r₂ : 𝓛-functor pr₁ ((x₂ , y₂) , to-Σ-≡ (p₂ , q₂)) ≡[ 𝓛 X ] (x₀ , p₀))
-- -- -- -- --        → transport Y (pr₁ (from-Σ-≡ r₁) ∙ pr₁ (from-Σ-≡ (r₂ ⁻¹))) y₁ ≡ y₂
-- -- -- -- --    exp x₀ x₁ x₂ y₁ y₂ p₀ p₁ p₂ q₁ q₂ r₁ r₂ = {!!}

-- -- -- -- --    𝕊¹-induction-on-loop : transport (λ - → transport A loop - ≡ -) 𝕊¹-induction-on-base (apd 𝕊¹-induction loop) ≡ l
-- -- -- -- --    𝕊¹-induction-on-loop =
-- -- -- -- --     {!!} ≡⟨ {!!} ⟩
-- -- -- -- --     {!!} ≡⟨ {!!} ⟩
-- -- -- -- --     {!!} ≡⟨ {!!} ⟩
-- -- -- -- --     {!!} ≡⟨ {!!} ⟩
-- -- -- -- --     l ∎

-- -- -- -- --    π : Σ A → 𝕊¹
-- -- -- -- --    π = pr₁


-- -- -- -- --    σ : (Σ y ꞉ A base , transport A loop y ≡ y)
-- -- -- -- --      → fiber (𝓛-functor π) (base , loop)
-- -- -- -- --    σ (y , m) = ((base , y) , (to-Σ-≡ (loop , m))) , to-Σ-≡ (refl , (ap-pr₁-to-Σ-≡ (loop , m)))

-- -- -- -- --    τ : fiber (𝓛-functor π) (base , loop)
-- -- -- -- --      → (Σ y ꞉ A base , transport A loop y ≡ y)
-- -- -- -- --    τ (((x , y) , 𝓁) , p) = γ (from-Σ-≡ p)
-- -- -- -- --     where
-- -- -- -- --      γ : (Σ p₁ ꞉ x ≡ base , transport (λ - → - ≡ -) p₁ (ap pr₁ 𝓁) ≡ loop)
-- -- -- -- --        → (Σ y ꞉ A base , transport A loop y ≡ y)
-- -- -- -- --      γ (refl , p₂) = y , (ψ ∙ pr₂ (from-Σ-≡ 𝓁))
-- -- -- -- --       where
-- -- -- -- --        ψ : transport A loop y ≡ transport A (pr₁ (from-Σ-≡ 𝓁)) y
-- -- -- -- --        ψ = ap (λ - → transport A - y) (p₂ ⁻¹ ∙ ap-pr₁-from-Σ-≡ 𝓁)

-- -- -- -- --    bar : fiber (𝓛-functor π) (base , loop)
-- -- -- -- --    bar = (((base , a) , l⁺) , to-Σ-≡ (refl , ap-pr₁-to-Σ-≡ (loop , l)))

-- -- -- -- --    test : Σ y ꞉ A base , transport A loop y ≡ y
-- -- -- -- --    test = τ bar

-- -- -- -- --    footest : σ (a , l) ≡ bar
-- -- -- -- --    footest = refl

-- -- -- -- --    ρ : 𝕊¹ → Σ A
-- -- -- -- --    ρ x = (x , 𝕊¹-induction x)

-- -- -- -- --    lem : pr₁ ∘ ρ ∼ id
-- -- -- -- --    lem x = refl

-- -- -- -- --    lem' : pr₁ ∘ ρ ≡ id
-- -- -- -- --    lem' = dfunext fe lem

-- -- -- -- --    baz : fiber (𝓛-functor π) (base , loop)
-- -- -- -- --    baz = (ρ base , ap ρ loop) , to-Σ-≡ (happly lem' base , γ)
-- -- -- -- --     where
-- -- -- -- --      γ : transport (λ - → - ≡ -) (happly lem' base) (ap pr₁ (ap ρ loop)) ≡ loop
-- -- -- -- --      γ = transport (λ - → - ≡ -) (happly lem' base) (ap pr₁ (ap ρ loop)) ≡⟨ refl ⟩
-- -- -- -- --          transport (λ - → - ≡ -) (ap (λ - → - base) lem') (ap pr₁ (ap ρ loop)) ≡⟨ (transport-ap (λ - → - ≡ -) (λ - → - base) lem') ⁻¹ ⟩
-- -- -- -- --          transport (λ - → - base ≡ - base) lem' (ap pr₁ (ap ρ loop)) ≡⟨ ap (transport (λ - → - base ≡ - base) lem') (ap-ap ρ pr₁ loop) ⟩
-- -- -- -- --          transport (λ - → - base ≡ - base) lem' (ap (pr₁ ∘ ρ) loop) ≡⟨ apd (λ - → ap - loop) lem' ⟩
-- -- -- -- --          ap id loop ≡⟨ ap-id-is-id loop ⟩
-- -- -- -- --          loop ∎

-- -- -- -- --    bleh : 𝓛-functor ρ (base , loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
-- -- -- -- --    bleh = to-Σ-≡ (to-Σ-≡ (refl , γ₁) , {!!})
-- -- -- -- --     where
-- -- -- -- --      γ₁ : pr₂ (ρ base) ≡ a
-- -- -- -- --      γ₁ = {!!}

-- -- -- -- --    blah : 𝓤 ⊔ 𝓥 ̇
-- -- -- -- --    blah = Σ α ꞉ (𝕊¹ → Σ A) , (α base , ap α loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)

-- -- -- -- --    blah-is-singleton : is-singleton blah
-- -- -- -- --    blah-is-singleton = 𝕊¹-uniqueness-principle (base , a) l⁺

-- -- -- -- --    map : (Σ y ꞉ A base , transport A loop y ≡ y) → 𝓛 (Σ A)
-- -- -- -- --    map (a₁ , l₁) = (base , a₁) , (to-Σ-≡ (loop , l₁))

-- -- -- -- --    𝕊¹-rec' : {B : 𝓦 ̇ } → 𝓛 B → 𝕊¹ → B
-- -- -- -- --    𝕊¹-rec' (b , p) = 𝕊¹-rec b p

-- -- -- -- --    kkk : (a₁ a₂ : A base) (l₁ : transport A loop a₁ ≡ a₁) (l₂ : transport A loop a₂ ≡ a₂)
-- -- -- -- --        → (a₁ , l₁) ≡ (a₂ , l₂)
-- -- -- -- --        → 𝕊¹-rec (base , a₁) (to-Σ-≡ (loop , l₁)) ≡ 𝕊¹-rec (base , a₂) (to-Σ-≡ (loop , l₂))
-- -- -- -- --    kkk a₁ a₂ l₁ l₂ p = ap (𝕊¹-rec' ∘ map) p

-- -- -- -- --    nnn : (a₁ a₂ : A base) (l₁ : transport A loop a₁ ≡ a₁) (l₂ : transport A loop a₂ ≡ a₂)
-- -- -- -- --        → 𝕊¹-rec (base , a₁) (to-Σ-≡ (loop , l₁)) ≡ 𝕊¹-rec (base , a₂) (to-Σ-≡ (loop , l₂))
-- -- -- -- --        → (a₁ , l₁) ≡ (a₂ , l₂)
-- -- -- -- --    nnn a₁ a₂ l₁ l₂ p = {!!}
-- -- -- -- --     where
-- -- -- -- --      r₁ : 𝕊¹ → Σ A
-- -- -- -- --      r₁ = 𝕊¹-rec (base , a₁) (to-Σ-≡ (loop , l₁))
-- -- -- -- --      r₂ : 𝕊¹ → Σ A
-- -- -- -- --      r₂ = 𝕊¹-rec (base , a₂) (to-Σ-≡ (loop , l₂))
-- -- -- -- --      e₁ : 𝓛-functor r₁ (base , loop) ≡ (base , a₁) , to-Σ-≡ (loop , l₁)
-- -- -- -- --      e₁ = 𝕊¹-rec-comp (base , a₁) (to-Σ-≡ (loop , l₁))

-- -- -- -- -- -- (transport-ap (λ - → - ≡ -) {!!} (ap pr₁ (ap ρ loop))) ⁻¹

-- -- -- -- --          {-
-- -- -- -- --       where
-- -- -- -- --        ψ :
-- -- -- -- --          -- transport (λ - → - base ≡ - base) lem' (ap (pr₁ ∘ ρ) loop)
-- -- -- -- --          ≡ ap id loop
-- -- -- -- --        ψ = apd (λ - → ap - loop) lem' -}
-- -- -- -- --     {-
-- -- -- -- --      γ : ap pr₁ (ap ρ loop) ≡ loop
-- -- -- -- --      γ = ap pr₁ (ap ρ loop) ≡⟨ ap-ap ρ pr₁ loop ⟩
-- -- -- -- --          ap (pr₁ ∘ ρ) loop  ≡⟨ {!!} ⟩
-- -- -- -- --          ap id loop         ≡⟨ ap-id-is-id loop ⟩
-- -- -- -- --          loop               ∎
-- -- -- -- --       where
-- -- -- -- --        ψ : transport (λ z → z base ≡ z base) lem' (ap (pr₁ ∘ ρ) loop) ≡
-- -- -- -- --              ap id loop
-- -- -- -- --        ψ = apd (λ - → ap - loop) lem'
-- -- -- -- --     -}

-- -- -- -- --      {- transport (λ - → - ≡ -) loop (ap pr₁ l⁺) ≡⟨ ? ⟩
-- -- -- -- --          transport (λ - → - ≡ -) loop (pr₁ (from-Σ-≡ l⁺)) ≡⟨ ? ⟩
-- -- -- -- --          transport (λ - → - ≡ -)
-- -- -- -- --      -}
-- -- -- -- --        {- transport A loop y               ≡⟨ {!!} ⟩
-- -- -- -- --            transport A (ap pr₁ 𝓁) y         ≡⟨ ap {!!} {!!} ⟩
-- -- -- -- --            transport A (pr₁ (from-Σ-≡ 𝓁)) y ∎ -}
-- -- -- -- --    {- (transport A p₁ y) , {!!}
-- -- -- -- --     where
-- -- -- -- --      l₁ : x ≡ x
-- -- -- -- --      l₁ = pr₁ (from-Σ-≡ 𝓁)
-- -- -- -- --      l₂ : transport A l₁ y ≡ y
-- -- -- -- --      l₂ = pr₂ (from-Σ-≡ 𝓁)
-- -- -- -- --      p₁ : x ≡ base
-- -- -- -- --      p₁ = pr₁ (from-Σ-≡ p)
-- -- -- -- --      p₂ : transport (λ - → - ≡ -) p₁ (ap pr₁ 𝓁) ≡ loop
-- -- -- -- --      p₂ = pr₂ (from-Σ-≡ p)
-- -- -- -- --      p₃ : transport (λ - → - ≡ -) p₁ l₁ ≡ loop
-- -- -- -- --      p₃ = ap (transport (λ - → - ≡ -) p₁) ((ap-pr₁-from-Σ-≡ 𝓁) ⁻¹) ∙ p₂
-- -- -- -- --    -}


-- -- -- -- -- --    ttt : transport A (pr₁ (from-Σ-≡ (𝕊¹-rec-on-base (base , a) l⁺))) (pr₂ (r base)) ≡ a
-- -- -- -- -- --    ttt =

-- -- -- -- -- --    lemma₁ : ρ ∼ r
-- -- -- -- -- --    lemma₁ x = to-Σ-≡ ((p ⁻¹) , γ)
-- -- -- -- -- --     where
-- -- -- -- -- --      p : pr₁ (r x) ≡ x
-- -- -- -- -- --      p = happly 𝕊¹-induction-key-lemma x
-- -- -- -- -- --      γ = transport A (p ⁻¹) (pr₂ (ρ x))                 ≡⟨ refl ⟩
-- -- -- -- -- --          transport A (p ⁻¹) (transport A p (pr₂ (r x))) ≡⟨ I    ⟩
-- -- -- -- -- --          transport A (p ∙ p ⁻¹) (pr₂ (r x))             ≡⟨ II   ⟩
-- -- -- -- -- --          transport A refl (pr₂ (r x))                   ≡⟨ refl ⟩
-- -- -- -- -- --          pr₂ (r x)                                      ∎
-- -- -- -- -- --       where
-- -- -- -- -- --        I  = (transport-comp A p (p ⁻¹)) ⁻¹
-- -- -- -- -- --        II = ap (λ - → transport A - (pr₂ (r x))) ((right-inverse p) ⁻¹)

-- -- -- -- -- --    lemma₂ : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] (r base , ap r loop)
-- -- -- -- -- --    lemma₂ = to-Σ-≡ ((lemma₁ base) , γ)
-- -- -- -- -- --      where
-- -- -- -- -- --       γ = transport (λ - → - ≡ -) (lemma₁ base) (ap ρ loop) ≡⟨ I  ⟩
-- -- -- -- -- --           lemma₁ base ⁻¹ ∙ ap ρ loop ∙ lemma₁ base          ≡⟨ II ⟩
-- -- -- -- -- --           ap r loop                                         ∎
-- -- -- -- -- --        where
-- -- -- -- -- --         I  = transport-along-≡-dup (lemma₁ base) (ap ρ loop)
-- -- -- -- -- --         II = homotopies-are-natural'' ρ r lemma₁ {base} {base} {loop}

-- -- -- -- -- --    lemma₃ : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
-- -- -- -- -- --    lemma₃ = lemma₂ ∙ 𝕊¹-rec-comp (base , a) l⁺

-- -- -- -- -- --    {-
-- -- -- -- -- --    lemma₁' : pr₁ ∘ ρ ∼ id
-- -- -- -- -- --    lemma₁' x = ap pr₁ (lemma₁ x) ∙ happly 𝕊¹-induction-key-lemma x

-- -- -- -- -- --    lemma₂' : (ρ base , ap ρ loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
-- -- -- -- -- --    lemma₂' = to-Σ-≡ ({!lemma₁' base!} , {!!})
-- -- -- -- -- --    -}

-- -- -- -- -- --    e₀ : ρ base ≡ base , a
-- -- -- -- -- --    e₀ = pr₁ (from-Σ-≡ lemma₃)

-- -- -- -- -- --    e₁ : pr₁ (ρ base) ≡ base
-- -- -- -- -- --    e₁ = pr₁ (from-Σ-≡ e₀)

-- -- -- -- -- --    t₁ : A base
-- -- -- -- -- --    t₁ = transport A e₁ (pr₂ (ρ base))

-- -- -- -- -- --    e₂ : t₁ ≡ a
-- -- -- -- -- --    e₂ = pr₂ (from-Σ-≡ e₀)

-- -- -- -- -- --    t₂ : base , a ≡ base , a
-- -- -- -- -- --    t₂ = transport (λ - → - ≡ -) e₀ (ap ρ loop)

-- -- -- -- -- --    e₃ : t₂ ≡ l⁺
-- -- -- -- -- --    e₃ = pr₂ (from-Σ-≡ lemma₃)

-- -- -- -- -- --    e₄ : transport (λ - → transport A (pr₁ (from-Σ-≡ -)) a ≡ a) e₃
-- -- -- -- -- --          (pr₂ (from-Σ-≡ t₂))
-- -- -- -- -- --       ≡ pr₂ (from-Σ-≡ l⁺)
-- -- -- -- -- --    e₄ = apd (pr₂ ∘ from-Σ-≡) e₃

-- -- -- -- -- --    testtest : transport A (ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)) (pr₂ (r base)) ≡ a
-- -- -- -- -- --    testtest = transport A (ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)) (pr₂ (r base)) ≡⟨ {!!} ⟩
-- -- -- -- -- --               {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- --               {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- --               transport A (happly 𝕊¹-induction-key-lemma base ∙ e₁)
-- -- -- -- -- --                 (pr₂ (r base)) ≡⟨ transport-comp A (happly 𝕊¹-induction-key-lemma base) e₁ ⟩
-- -- -- -- -- --               transport A e₁ (transport A (happly 𝕊¹-induction-key-lemma base) (pr₂ (r base))) ≡⟨ e₂ ⟩
-- -- -- -- -- --               a ∎

-- -- -- -- -- --    𝕊¹-induction : (x : 𝕊¹) → A x
-- -- -- -- -- --    𝕊¹-induction x = transport A p (raw-𝕊¹-induction x)
-- -- -- -- -- --     where
-- -- -- -- -- --      p : pr₁ (ρ x) ≡ x
-- -- -- -- -- --      p = (happly 𝕊¹-induction-key-lemma x ⁻¹) ∙ {!lemma₁ x!} -- lemma₁' x


-- -- -- -- -- -- --    κ : transport A (pr₁ (from-Σ-≡ (ap pr₁ lemma₃))) (pr₂ (ρ base)) ≡ a
-- -- -- -- -- -- --    κ = pr₂ (from-Σ-≡ (ap pr₁ lemma₃))

-- -- -- -- -- -- --    κ' : transport A (pr₁ (from-Σ-≡ (lemma₁ base))) (pr₂ (ρ base)) ≡
-- -- -- -- -- -- --           pr₂ (r base)
-- -- -- -- -- -- --    κ' = pr₂ (from-Σ-≡ (lemma₁ base))

-- -- -- -- -- -- --    𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
-- -- -- -- -- -- --                      ≡[ Σ y ꞉ A base , transport A loop y ≡ y ]
-- -- -- -- -- -- --                        (a , l)
-- -- -- -- -- -- --    𝕊¹-induction-comp = to-Σ-≡ (γ₁ , {!!})
-- -- -- -- -- -- --     where
-- -- -- -- -- -- --      p : pr₁ (ρ base) ≡ base
-- -- -- -- -- -- --      p = {!!} -- lemma₁' base
-- -- -- -- -- -- --      γ₁ : 𝕊¹-induction base ≡ a
-- -- -- -- -- -- --      γ₁ = 𝕊¹-induction base ≡⟨ refl ⟩
-- -- -- -- -- -- --           transport A p (raw-𝕊¹-induction base) ≡⟨ {!!} ⟩
-- -- -- -- -- -- --           {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- --           {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- --           a ∎



-- -- -- -- -- -- -- --    κ⁺ : {!!} ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- --    κ⁺ = {!!}

-- -- -- -- -- -- -- --    κ₁ : transport A (ap (pr₁ ∘ pr₁) lemma₃) (raw-𝕊¹-induction base) ≡ a
-- -- -- -- -- -- -- --    κ₁ = {!!}

-- -- -- -- -- -- -- --    κ₂ : transport (λ z → transport A (pr₁ (from-Σ-≡ z)) a ≡ a)
-- -- -- -- -- -- -- --           (pr₂ (from-Σ-≡ lemma₃))
-- -- -- -- -- -- -- --           (pr₂
-- -- -- -- -- -- -- --            (from-Σ-≡
-- -- -- -- -- -- -- --             (transport (λ x → x ≡ x) (pr₁ (from-Σ-≡ lemma₃)) (ap ρ loop))))
-- -- -- -- -- -- -- --           ≡ {!!} -- pr₂ (loop , l) -- pr₂ (from-Σ-≡ (to-Σ-≡ (loop , l))) -- pr₂ (from-Σ-≡ l⁺)
-- -- -- -- -- -- -- --    -- transport (λ x → x ≡ x) (pr₁ (from-Σ-≡ lemma₃)) (ap ρ loop) ≡ l⁺
-- -- -- -- -- -- -- --    κ₂ = apd (pr₂ ∘ from-Σ-≡) (pr₂ (from-Σ-≡ lemma₃)) ∙ {!!}

-- -- -- -- -- -- -- -- --    final : (ι base , apd ι loop) ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- -- --    final = to-Σ-≡ (γ₁ , {!!})
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --      γ₁ : ι base ≡ a
-- -- -- -- -- -- -- -- --      γ₁ = {!!}
-- -- -- -- -- -- -- -- --      ψ : transport A (pr₁ (from-Σ-≡ (ap pr₁ 𝓛-bar))) (ι base) ≡ a
-- -- -- -- -- -- -- -- --      ψ = pr₂ (from-Σ-≡ (ap pr₁ 𝓛-bar))


-- -- -- -- -- -- -- -- --    π : Σ A → 𝕊¹
-- -- -- -- -- -- -- -- --    π = pr₁

-- -- -- -- -- -- -- -- --    fff : fiber (𝓛-functor π) (base , loop)
-- -- -- -- -- -- -- -- --    fff = ((base , a) , l⁺) , to-Σ-≡ (refl , (ap-pr₁-to-Σ-≡ (loop , l)))

-- -- -- -- -- -- -- -- --    ggg : fiber (𝓛-functor π) (base , loop)
-- -- -- -- -- -- -- -- --    ggg = (𝓛-functor r (base , loop)) , (II ∙ III)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     II  = ap (𝓛-functor pr₁) (𝕊¹-rec-comp (base , a) l⁺)
-- -- -- -- -- -- -- -- --     III = ap (λ - → (base , -)) (ap-pr₁-to-Σ-≡ (loop , l))

-- -- -- -- -- -- -- -- --    κ-transition : (Σ A) → (Σ A)
-- -- -- -- -- -- -- -- --    κ-transition (x , a) = (pr₁ (r x)) , (back-transport A p a)
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --      p : pr₁ (r x) ≡ x
-- -- -- -- -- -- -- -- --      p = (happly 𝕊¹-induction-key-lemma x)

-- -- -- -- -- -- -- -- --    ι : (x : 𝕊¹) → A x
-- -- -- -- -- -- -- -- --    ι x = 𝕊¹-induction x

-- -- -- -- -- -- -- -- --    δ : 𝕊¹ → Σ A
-- -- -- -- -- -- -- -- --    δ x = (x , ι x)


-- -- -- -- -- -- -- -- --    fibtest : {X : 𝓦 ̇ } {Y : 𝓦' ̇ } (f : X → Y) {x x' : X} (p : x' ≡ x) {y : Y}
-- -- -- -- -- -- -- -- --              (q : f x ≡ y)
-- -- -- -- -- -- -- -- --            → (x' , (ap f p ∙ q)) ≡[ fiber f y ] (x , q)
-- -- -- -- -- -- -- -- --    fibtest f refl refl = refl

-- -- -- -- -- -- -- -- --    fibbar : ((𝓛-functor δ (base , loop)) , (ap (𝓛-functor π) (𝓛-foo) ∙ pr₂ ggg)) ≡[ fiber (𝓛-functor π) (base , loop) ] ggg
-- -- -- -- -- -- -- -- --    fibbar = fibtest (𝓛-functor π) 𝓛-foo (pr₂ ggg)


-- -- -- -- -- -- -- -- --    σ : fiber (𝓛-functor π) (base , loop)
-- -- -- -- -- -- -- -- --      → Σ y ꞉ A base , transport A loop y ≡ y
-- -- -- -- -- -- -- -- --    σ (((x , a) , 𝓁) , q) = γ (pr₁ (from-Σ-≡ q)) (pr₂ (from-Σ-≡ q))
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --      γ : (q₁ : pr₁ (𝓛-functor π ((x , a) , 𝓁)) ≡ base) (q₂ : transport {!!} {!!} q₁ ≡ {!!}) → Σ y ꞉ A base , transport A loop y ≡ y
-- -- -- -- -- -- -- -- --      γ refl q₂ = {!!}

-- -- -- -- -- -- -- -- --    final : (ι base , apd ι loop) ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- -- --    final = to-Σ-≡ (γ₁ , {!!})
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --      γ₁ : ι base ≡ a
-- -- -- -- -- -- -- -- --      γ₁ = {!!}
-- -- -- -- -- -- -- -- --      ψ : transport A (pr₁ (from-Σ-≡ (ap pr₁ 𝓛-bar))) (ι base) ≡ a
-- -- -- -- -- -- -- -- --      ψ = pr₂ (from-Σ-≡ (ap pr₁ 𝓛-bar))




-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- --    hhh : fiber (𝓛-functor π) (base , loop)
-- -- -- -- -- -- -- -- --    hhh = 𝓛-functor-dep ι (base , loop) , {!!}
-- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- --   foo : 𝓛 (Σ A) → 𝓛 𝕊¹
-- -- -- -- -- -- -- -- -- --   foo = 𝓛-functor pr₁

-- -- -- -- -- -- -- -- -- --   comp : (r base , ap r loop) ≡[ 𝓛 (Σ A) ] ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- --   comp = 𝕊¹-rec-comp (base , a) l⁺

-- -- -- -- -- -- -- -- -- --   comp' : (pr₁ (r base) , ap pr₁ (ap r loop)) ≡[ 𝓛 𝕊¹ ] (base , ap pr₁ l⁺)
-- -- -- -- -- -- -- -- -- --   comp' = ap foo comp

-- -- -- -- -- -- -- -- -- --   baz : 𝓛 𝕊¹ → 𝓛 (Σ A)
-- -- -- -- -- -- -- -- -- --   baz = 𝓛-functor r

-- -- -- -- -- -- -- -- -- --   𝓛-functor-dep : {X : 𝓦 ̇ } {Y : X → 𝓦' ̇ } (f : (x : X) → Y x) → 𝓛 X → 𝓛 (Σ Y)
-- -- -- -- -- -- -- -- -- --   𝓛-functor-dep f (x , p) = (x , f x) , to-Σ-≡ (p , (apd f p))

-- -- -- -- -- -- -- -- -- --   testtest : {X : 𝓦 ̇ } {Y : X → 𝓦' ̇ } (x₀ : X) (p₀ : x₀ ≡ x₀)
-- -- -- -- -- -- -- -- -- --              (u v : Σ Y) (q₁ : pr₁ u ≡ x₀) (q₂ : pr₁ u ≡ x₀)
-- -- -- -- -- -- -- -- -- --            → u ≡ v → (transport Y q₁ (pr₂ u)) , {!!} ≡[ Σ y ꞉ Y x₀ , transport Y p₀ y ≡ y ] {!!}
-- -- -- -- -- -- -- -- -- --   testtest = {!!}

-- -- -- -- -- -- -- -- -- --   ι : (x : 𝕊¹) → A x
-- -- -- -- -- -- -- -- -- --   ι = {!!}

-- -- -- -- -- -- -- -- -- --   ω : 𝓛 𝕊¹ → 𝓛 (Σ A)
-- -- -- -- -- -- -- -- -- --   ω = 𝓛-functor-dep ι

-- -- -- -- -- -- -- -- -- --   blah : ω (base , loop) ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- --   blah = {!!}

-- -- -- -- -- -- -- -- -- --   blahblah : (ι base , apd ι loop) ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- -- -- --   blahblah = {!!}

-- -- -- -- -- -- -- -- -- --   {-
-- -- -- -- -- -- -- -- -- --     So we get the map:
-- -- -- -- -- -- -- -- -- --       ω = 𝓛-functor-dep ι : 𝓛 𝕊¹ → 𝓛 (Σ A)

-- -- -- -- -- -- -- -- -- --       ap ω comp' : ω (pr₁ (r base) , ap pr₁ (ap r loop)) ≡ ω (base , loop)
-- -- -- -- -- -- -- -- -- --       ap ω comp' = ap (ω ∘ foo) comp

-- -- -- -- -- -- -- -- -- --     We also know that:
-- -- -- -- -- -- -- -- -- --       baz (base , loop) = (r base , ap r loop) ≡ ((base , a) , l)

-- -- -- -- -- -- -- -- -- --   -}
-- -- -- -- -- -- -- -- -- --   -- We can show that pr₁ ∘ r ≡ id, so 𝓛-functor pr₁ ∘ 𝓛-functor r ≡ id too.
-- -- -- -- -- -- -- -- -- --   -- 𝕊¹-induction = ι : (x : 𝕊¹) → A (x)
-- -- -- -- -- -- -- -- -- --   -- Question: (ι base , apd ι loop) ≡[ 𝓛 (Σ v ꞉ (u : Σ A , pr₁ u ≡ base) , v ≡ v) ] (a , l) ???
-- -- -- -- -- -- -- -- -- --   {-


-- -- -- -- -- -- -- -- -- --      (Σ v ꞉ (u : Σ A , pr₁ u ≡ base) , v ≡ v)

-- -- -- -- -- -- -- -- -- --   -}

-- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
-- -- -- -- -- -- -- -- -- -- -- --                     ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)

-- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-≡ : ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop)
-- -- -- -- -- -- -- -- -- --                      ≡[ Σ x ꞉ 𝕊¹ , x ≡ x ] (base , loop)
-- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-≡ = to-Σ-≡ (ap pr₁ e , γ)
-- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- --     e : r base ≡ base , a
-- -- -- -- -- -- -- -- -- --     e = 𝕊¹-rec-on-base (base , a) l⁺
-- -- -- -- -- -- -- -- -- --     γ = transport (λ - → - ≡ -) (ap pr₁ e) (ap (pr₁ ∘ r) loop) ≡⟨ I    ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ (ap (pr₁ ∘ r) loop ∙ ap pr₁ e)           ≡⟨ II   ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ ap pr₁ e)          ≡⟨ III  ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ ap pr₁ (ap r loop ∙ e)                   ≡⟨ IV   ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ (e ⁻¹) ∙ ap pr₁ (ap r loop ∙ e)                 ≡⟨ V    ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ (e ⁻¹ ∙ (ap r loop ∙ e))                        ≡⟨ VI   ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ (transport (λ - → - ≡ -) e (ap r loop))         ≡⟨ VII  ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ l⁺                                              ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- --         ap pr₁ (pr₂ _)                             ≡⟨ VIII ⟩
-- -- -- -- -- -- -- -- -- --         loop                                                   ∎
-- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- --       I    = transport-along-≡-dup (ap pr₁ e) (ap (pr₁ ∘ r) loop)
-- -- -- -- -- -- -- -- -- --       II   = ap (λ - → ap pr₁ e ⁻¹ ∙ (- ∙ ap pr₁ e)) ((ap-ap r pr₁ loop) ⁻¹)
-- -- -- -- -- -- -- -- -- --       III  = ap (λ - → ap pr₁ e ⁻¹ ∙ -) ((ap-∙ pr₁ (ap r loop) e) ⁻¹)
-- -- -- -- -- -- -- -- -- --       IV   = ap (λ - → - ∙ ap pr₁ (ap r loop ∙ e)) (ap-sym pr₁ e)
-- -- -- -- -- -- -- -- -- --       V    = (ap-∙ pr₁ (e ⁻¹) (ap r loop ∙ e)) ⁻¹
-- -- -- -- -- -- -- -- -- --       VI   = ap (ap pr₁) ((transport-along-≡-dup e (ap r loop)) ⁻¹)
-- -- -- -- -- -- -- -- -- --       VII  = ap (ap pr₁) (𝕊¹-rec-on-loop (base , a) l⁺)
-- -- -- -- -- -- -- -- -- --       VIII = {!!}

-- -- -- -- -- -- -- -- -- -- --  module 𝕊¹-induction
-- -- -- -- -- -- -- -- -- -- --          (A : 𝕊¹ → 𝓥 ̇ )
-- -- -- -- -- -- -- -- -- -- --          (a : A base)
-- -- -- -- -- -- -- -- -- -- --          (l : transport A loop a ≡ a)
-- -- -- -- -- -- -- -- -- -- --         where

-- -- -- -- -- -- -- -- -- -- --   l⁺ : (base , a) ≡ (base , a)
-- -- -- -- -- -- -- -- -- -- --   l⁺ = to-Σ-≡ (loop , l)

-- -- -- -- -- -- -- -- -- -- --   r : 𝕊¹ → Σ A
-- -- -- -- -- -- -- -- -- -- --   r = 𝕊¹-rec (base , a) l⁺

-- -- -- -- -- -- -- -- -- -- -- \end{code}

-- -- -- -- -- -- -- -- -- -- -- Note that pr₁ ∘ r : 𝕊¹ → 𝕊¹. We wish to show that it is equal to the identity.
-- -- -- -- -- -- -- -- -- -- -- This would tell us that for every x : 𝕊¹ we have r(x) = (x , a) for some
-- -- -- -- -- -- -- -- -- -- -- a : A(x), which yields the induction principle.

-- -- -- -- -- -- -- -- -- -- -- \begin{code}

-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-≡ : ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop)
-- -- -- -- -- -- -- -- -- -- --                      ≡[ Σ x ꞉ 𝕊¹ , x ≡ x ] (base , loop)
-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-≡ = to-Σ-≡ (ap pr₁ e , γ)
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --     e : 𝕊¹-rec (base , a) l⁺ base ≡ base , a
-- -- -- -- -- -- -- -- -- -- --     e = 𝕊¹-rec-on-base (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- --     γ = transport (λ - → - ≡ -) (ap pr₁ e) (ap (pr₁ ∘ r) loop) ≡⟨ I    ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ (ap (pr₁ ∘ r) loop ∙ ap pr₁ e)           ≡⟨ II   ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ ap pr₁ e)          ≡⟨ III  ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ e ⁻¹ ∙ ap pr₁ (ap r loop ∙ e)                   ≡⟨ IV   ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ (e ⁻¹) ∙ ap pr₁ (ap r loop ∙ e)                 ≡⟨ V    ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ (e ⁻¹ ∙ (ap r loop ∙ e))                        ≡⟨ VI   ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ (transport (λ - → - ≡ -) e (ap r loop))         ≡⟨ VII  ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ l⁺                                              ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- --         ap pr₁ (to-Σ-≡ (loop , l))                             ≡⟨ VIII ⟩
-- -- -- -- -- -- -- -- -- -- --         loop                                                   ∎
-- -- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- -- --       I    = transport-along-≡-dup (ap pr₁ e) (ap (pr₁ ∘ r) loop)
-- -- -- -- -- -- -- -- -- -- --       II   = ap (λ - → ap pr₁ e ⁻¹ ∙ (- ∙ ap pr₁ e)) ((ap-ap r pr₁ loop) ⁻¹)
-- -- -- -- -- -- -- -- -- -- --       III  = ap (λ - → ap pr₁ e ⁻¹ ∙ -) ((ap-∙ pr₁ (ap r loop) e) ⁻¹)
-- -- -- -- -- -- -- -- -- -- --       IV   = ap (λ - → - ∙ ap pr₁ (ap r loop ∙ e)) (ap-sym pr₁ e)
-- -- -- -- -- -- -- -- -- -- --       V    = (ap-∙ pr₁ (e ⁻¹) (ap r loop ∙ e)) ⁻¹
-- -- -- -- -- -- -- -- -- -- --       VI   = ap (ap pr₁) ((transport-along-≡-dup e (ap r loop)) ⁻¹)
-- -- -- -- -- -- -- -- -- -- --       VII  = ap (ap pr₁) (𝕊¹-rec-on-loop (base , a) l⁺)
-- -- -- -- -- -- -- -- -- -- --       VIII = ap-pr₁-to-Σ-≡ (loop , l)

-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-lemma : pr₁ ∘ r ≡ id
-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-lemma =
-- -- -- -- -- -- -- -- -- -- --    pr₁ (from-Σ-≡ (singletons-are-props (𝕊¹-uniqueness-principle base loop)
-- -- -- -- -- -- -- -- -- -- --             (pr₁ ∘ r , 𝕊¹-induction-key-≡              )
-- -- -- -- -- -- -- -- -- -- --             (id      , to-Σ-≡ (refl , ap-id-is-id loop))))

-- -- -- -- -- -- -- -- -- -- --   zzz : (pr₁ ∘ r , 𝕊¹-induction-key-≡)
-- -- -- -- -- -- -- -- -- -- --       ≡ (id      , to-Σ-≡ (refl , ap-id-is-id loop))
-- -- -- -- -- -- -- -- -- -- --   zzz = singletons-are-props (𝕊¹-uniqueness-principle base loop)
-- -- -- -- -- -- -- -- -- -- --          (pr₁ ∘ r , 𝕊¹-induction-key-≡         )
-- -- -- -- -- -- -- -- -- -- --          (id , to-Σ-≡ (refl , ap-id-is-id loop))

-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction : (x : 𝕊¹) → A x
-- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction x = transport A (happly 𝕊¹-induction-key-lemma x) (pr₂ (r x))

-- -- -- -- -- -- -- -- -- -- --   -- TO DO: Consider something like (Σ s ꞉ Σ A , Σ 𝓵 : s ≡ s , ap pr₁ 𝓁 ≡ loop)???

-- -- -- -- -- -- -- -- -- -- --   open import UF-EquivalenceExamples

-- -- -- -- -- -- -- -- -- -- --   blah : (a : A base)
-- -- -- -- -- -- -- -- -- -- --        → (Σ 𝓁 ꞉ ((base , a) ≡[ Σ A ] (base , a)) , loop ≡ pr₁ (from-Σ-≡ 𝓁)) ≃ (transport A loop a ≡ a)
-- -- -- -- -- -- -- -- -- -- --   blah a = (Σ 𝓁 ꞉ ((base , a) ≡[ Σ A ] (base , a)) , loop ≡ pr₁ (from-Σ-≡ 𝓁)) ≃⟨ ≃-sym (Σ-change-of-variable (λ 𝓁 → loop ≡ pr₁ (from-Σ-≡ 𝓁)) ⌜ Σ-≡-≃ ⌝⁻¹ (⌜⌝-is-equiv (≃-sym Σ-≡-≃))) ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ w ꞉ (Σ p ꞉ base ≡ base , transport A p a ≡ a) , loop ≡ pr₁ (from-Σ-≡ (⌜ Σ-≡-≃ ⌝⁻¹ w))) ≃⟨ Σ-assoc ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ p ꞉ base ≡ base , Σ q ꞉ transport A p a ≡ a , loop ≡ pr₁ (from-Σ-≡ (⌜ Σ-≡-≃ ⌝⁻¹ (p , q)))) ≃⟨ Σ-cong (λ p → Σ-cong (λ q → ≡-cong loop (pr₁ (from-Σ-≡ (pr₁ (pr₁ (pr₂ Σ-≡-≃)) (p , q)))) refl (ap pr₁ (inverses-are-sections ⌜ Σ-≡-≃ ⌝ (⌜⌝-is-equiv Σ-≡-≃) (p , q))))) ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ p ꞉ base ≡ base , Σ q ꞉ transport A p a ≡ a , loop ≡ p) ≃⟨ ≃-refl _ ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ p ꞉ base ≡ base , (transport A p a ≡ a) × (loop ≡ p)) ≃⟨ Σ-cong (λ p → ×-comm) ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ p ꞉ base ≡ base , (loop ≡ p) × (transport A p a ≡ a)) ≃⟨ ≃-sym Σ-assoc ⟩
-- -- -- -- -- -- -- -- -- -- --              (Σ u ꞉ (Σ p ꞉ base ≡ base , loop ≡ p) , transport A (pr₁ u) a ≡ a) ≃⟨ ≃-sym (Σ-change-of-variable (λ u → transport A (pr₁ u) a ≡ a) ⌜ singleton-≃-𝟙' (singleton-types-are-singletons loop) ⌝ (⌜⌝-is-equiv (singleton-≃-𝟙' (singleton-types-are-singletons loop)))) ⟩
-- -- -- -- -- -- -- -- -- -- --              𝟙{𝓤₀} × (transport A loop a ≡ a) ≃⟨ 𝟙-lneutral ⟩
-- -- -- -- -- -- -- -- -- -- --              (transport A loop a ≡ a) ■

-- -- -- -- -- -- -- -- -- -- --   blah' : (Σ a ꞉ A base , Σ 𝓁 ꞉ ((base , a) ≡[ Σ A ] (base , a)) , loop ≡ pr₁ (from-Σ-≡ 𝓁)) ≃ (Σ a ꞉ A base , (transport A loop a ≡ a))
-- -- -- -- -- -- -- -- -- -- --   blah' = Σ-cong blah

-- -- -- -- -- -- -- -- -- -- --   blah'' : (Σ s ꞉ Σ A , Σ 𝓁 ꞉ s ≡ s , Σ p ꞉ base ≡ pr₁ s , loop ≡ transport (λ - → - ≡ -) (p ⁻¹) (pr₁ (from-Σ-≡ 𝓁)))
-- -- -- -- -- -- -- -- -- -- --          ≃ (Σ a ꞉ A base , Σ 𝓁 ꞉ ((base , a) ≡[ Σ A ] (base , a)) , loop ≡ pr₁ (from-Σ-≡ 𝓁))
-- -- -- -- -- -- -- -- -- -- --   blah'' = {!!}

-- -- -- -- -- -- -- -- -- -- --   wut : (Σ s ꞉ Σ A , Σ 𝓁 ꞉ s ≡ s , Σ p ꞉ base ≡ pr₁ s , loop ≡ transport (λ - → - ≡ -) (p ⁻¹) (pr₁ (from-Σ-≡ 𝓁)))
-- -- -- -- -- -- -- -- -- -- --   wut = (base , a) , (l⁺ , (refl , ap pr₁ ((fromto-Σ-≡ (loop , l)) ⁻¹)))

-- -- -- -- -- -- -- -- -- -- --   wut' : (Σ s ꞉ Σ A , Σ 𝓁 ꞉ s ≡ s , Σ p ꞉ pr₁ s ≡ base , transport (λ - → - ≡ -) p (pr₁ (from-Σ-≡ 𝓁)) ≡ loop)
-- -- -- -- -- -- -- -- -- -- --   wut' = (r base) , (ap r loop , (pr₁ (from-Σ-≡ κ)) , (ap (transport (λ - → - ≡ -) (pr₁ (from-Σ-≡ κ))) ({!!} ∙ ap-ap r pr₁ loop) ∙ pr₂ (from-Σ-≡ κ))) -- from-Σ-≡ {!κ!})
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --     κ : (pr₁ ∘ r) base , ap (pr₁ ∘ r) loop ≡ (base , loop)
-- -- -- -- -- -- -- -- -- -- --     κ = 𝕊¹-induction-key-≡
-- -- -- -- -- -- -- -- -- -- --     foo : (r base , ap r loop) ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- --     foo = 𝕊¹-rec-comp (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- --     foo₁ : r base ≡ (base , a)
-- -- -- -- -- -- -- -- -- -- --     foo₁ = 𝕊¹-rec-on-base (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- --     foo₂ : transport (λ - → - ≡ -) foo₁ (ap r loop) ≡ l⁺
-- -- -- -- -- -- -- -- -- -- --     foo₂ = 𝕊¹-rec-on-loop (base , a) l⁺

-- -- -- -- -- -- -- -- -- -- --   wut'' : (Σ s ꞉ Σ A , Σ 𝓁 ꞉ s ≡ s , Σ p ꞉ pr₁ s ≡ base , transport (λ - → - ≡ -) p (pr₁ (from-Σ-≡ 𝓁)) ≡ loop)
-- -- -- -- -- -- -- -- -- -- --   wut'' = (base , 𝕊¹-induction base) , ((to-Σ-≡ (loop , apd 𝕊¹-induction loop)) , refl , (ap pr₁ (fromto-Σ-≡ (loop , apd 𝕊¹-induction loop))))

-- -- -- -- -- -- -- -- -- -- --   wat : wut' ≡ wut''
-- -- -- -- -- -- -- -- -- -- --   wat = to-Σ-≡ (to-Σ-≡ ({!!} , {!!}) , {!!})
-- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- --     type₁ : Σ A
-- -- -- -- -- -- -- -- -- -- --     type₁ = pr₁ wut'

-- -- -- -- -- -- -- -- -- -- -- --   σ : (Σ a' ꞉ A base , transport A loop a' ≡ a') → (Σ s ꞉ Σ A , s ≡ s)
-- -- -- -- -- -- -- -- -- -- -- --   σ (a' , l') = ((base , a') , to-Σ-≡ (loop , l'))

-- -- -- -- -- -- -- -- -- -- -- --   σ-lc : left-cancellable σ
-- -- -- -- -- -- -- -- -- -- -- --   σ-lc {(a₁ , l₁)} {(a₂ , l₂)} p = to-Σ-≡ (r₁ , {!!})
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --     p₁ : (base , a₁) ≡ (base , a₂)
-- -- -- -- -- -- -- -- -- -- -- --     p₁ = pr₁ (from-Σ-≡ p)
-- -- -- -- -- -- -- -- -- -- -- --     p₂ : transport (λ - → - ≡ -) p₁ (to-Σ-≡ (loop , l₁)) ≡ to-Σ-≡ (loop , l₂)
-- -- -- -- -- -- -- -- -- -- -- --     p₂ = pr₂ (from-Σ-≡ p)
-- -- -- -- -- -- -- -- -- -- -- --     q₁ : base ≡ base
-- -- -- -- -- -- -- -- -- -- -- --     q₁ = pr₁ (from-Σ-≡ p₁)
-- -- -- -- -- -- -- -- -- -- -- --     q₂ : transport A q₁ a₁ ≡ a₂
-- -- -- -- -- -- -- -- -- -- -- --     q₂ = pr₂ (from-Σ-≡ p₁)
-- -- -- -- -- -- -- -- -- -- -- --     r₁ : a₁ ≡ a₂
-- -- -- -- -- -- -- -- -- -- -- --     r₁ = {!!}

-- -- -- -- -- -- -- -- -- -- -- --   τ : (Σ a' ꞉ A base , transport A loop a' ≡ a')
-- -- -- -- -- -- -- -- -- -- -- --     → (Σ a' ꞉ A base , (base , a') ≡ (base , a'))
-- -- -- -- -- -- -- -- -- -- -- --   τ (a' , l') = (a' , to-Σ-≡ (loop , l'))

-- -- -- -- -- -- -- -- -- -- -- --   τr : (Σ a' ꞉ A base , (base , a') ≡[ Σ A ] (base , a'))
-- -- -- -- -- -- -- -- -- -- -- --      → (Σ a' ꞉ A base , transport A loop a' ≡ a')
-- -- -- -- -- -- -- -- -- -- -- --   τr (a' , 𝓁) = (a' , {!!})

-- -- -- -- -- -- -- -- -- -- -- --   τ-lc : left-cancellable τ
-- -- -- -- -- -- -- -- -- -- -- --   τ-lc {(a₁ , l₁)} {(a₂ , l₂)} p = to-Σ-≡ (q₁ , q₂)
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --     p₁ : a₁ ≡ a₂
-- -- -- -- -- -- -- -- -- -- -- --     p₁ = pr₁ (from-Σ-≡ p)
-- -- -- -- -- -- -- -- -- -- -- --     p₂ : transport (λ - → (base , -) ≡ (base , -)) p₁ (to-Σ-≡ (loop , l₁)) ≡ to-Σ-≡ (loop , l₂)
-- -- -- -- -- -- -- -- -- -- -- --     p₂ = pr₂ (from-Σ-≡ p)
-- -- -- -- -- -- -- -- -- -- -- --     q₁ : a₁ ≡ a₂
-- -- -- -- -- -- -- -- -- -- -- --     q₁ = p₁
-- -- -- -- -- -- -- -- -- -- -- --     q₂ : transport (λ - → transport A loop - ≡ -) p₁ l₁ ≡ l₂
-- -- -- -- -- -- -- -- -- -- -- --     q₂ = transport (λ - → transport A loop - ≡ -) p₁ l₁ ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --          {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --          {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --          {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --          pr₂ (loop , l₂) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --          l₂ ∎
-- -- -- -- -- -- -- -- -- -- -- --     r₁ : from-Σ-≡ (transport (λ - → base , - ≡ base , -) p₁ (to-Σ-≡ (loop , l₁))) ≡ from-Σ-≡ (to-Σ-≡ (loop , l₂))
-- -- -- -- -- -- -- -- -- -- -- --     r₁ = ap from-Σ-≡ p₂
-- -- -- -- -- -- -- -- -- -- -- --     r₂ : {!!} ≡ l₂
-- -- -- -- -- -- -- -- -- -- -- --     r₂ = {!ap pr₂ r₁!} -- pr₂ (from-Σ-≡ p₂)




-- -- -- -- -- -- -- -- -- -- -- --   foofoo : σ (𝕊¹-induction base , apd 𝕊¹-induction loop) ≡ (r base , ap r loop)
-- -- -- -- -- -- -- -- -- -- -- --   foofoo = to-Σ-≡ ((to-Σ-≡ ((ψ ⁻¹) , ψ₂)) , γ)
-- -- -- -- -- -- -- -- -- -- -- --    where
-- -- -- -- -- -- -- -- -- -- -- --     ψ : (pr₁ ∘ r) base ≡ id base
-- -- -- -- -- -- -- -- -- -- -- --     ψ = happly 𝕊¹-induction-key-lemma base
-- -- -- -- -- -- -- -- -- -- -- --     ψ₂ : transport A (ψ ⁻¹) (𝕊¹-induction base) ≡ pr₂ (r base)
-- -- -- -- -- -- -- -- -- -- -- --     ψ₂ = transport A (ψ ⁻¹) (𝕊¹-induction base) ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- --          transport A (ψ ⁻¹) (transport A ψ (pr₂ (r base))) ≡⟨ (transport-comp A ψ (ψ ⁻¹)) ⁻¹ ⟩
-- -- -- -- -- -- -- -- -- -- -- --          transport A (ψ ∙ ψ ⁻¹) (pr₂ (r base)) ≡⟨ ap (λ - → transport A - (pr₂ (r base))) ((right-inverse ψ) ⁻¹) ⟩
-- -- -- -- -- -- -- -- -- -- -- --          pr₂ (r base) ∎
-- -- -- -- -- -- -- -- -- -- -- --     γ : transport (λ - → - ≡ -) (to-Σ-≡ ((ψ ⁻¹) , ψ₂)) (to-Σ-≡ (loop , apd 𝕊¹-induction loop))
-- -- -- -- -- -- -- -- -- -- -- --           ≡ ap r loop
-- -- -- -- -- -- -- -- -- -- -- --     γ = transport (λ - → - ≡ -) d₁ 𝓁 ≡⟨ transport-along-≡-dup d₁ 𝓁 ⟩
-- -- -- -- -- -- -- -- -- -- -- --         d₁ ⁻¹ ∙ (𝓁 ∙ d₁) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --         {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --         c₁ ∙ (l⁺ ∙ c₁ ⁻¹) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- --         (c₁ ⁻¹) ⁻¹ ∙ (l⁺ ∙ c₁ ⁻¹) ≡⟨ (transport-along-≡-dup (c₁ ⁻¹) l⁺) ⁻¹ ⟩
-- -- -- -- -- -- -- -- -- -- -- --         transport (λ - → - ≡ -) (c₁ ⁻¹) l⁺ ≡⟨ barbar ⁻¹ ⟩
-- -- -- -- -- -- -- -- -- -- -- --         ap r loop ∎
-- -- -- -- -- -- -- -- -- -- -- --      where
-- -- -- -- -- -- -- -- -- -- -- --       𝓁 : base , 𝕊¹-induction base ≡ base , 𝕊¹-induction base
-- -- -- -- -- -- -- -- -- -- -- --       𝓁 = to-Σ-≡ (loop , apd 𝕊¹-induction loop)
-- -- -- -- -- -- -- -- -- -- -- --       d₁ : (base , 𝕊¹-induction base) ≡ r base
-- -- -- -- -- -- -- -- -- -- -- --       d₁ = to-Σ-≡ ((ψ ⁻¹) , ψ₂)
-- -- -- -- -- -- -- -- -- -- -- --       c₁ : r base ≡ base , a
-- -- -- -- -- -- -- -- -- -- -- --       c₁ = (𝕊¹-rec-on-base (base , a) l⁺)
-- -- -- -- -- -- -- -- -- -- -- --       bazbaz : transport (λ - → - ≡ -) c₁ (ap r loop) ≡ l⁺
-- -- -- -- -- -- -- -- -- -- -- --       bazbaz = 𝕊¹-rec-on-loop (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- --       barbar : ap r loop ≡ transport (λ - → - ≡ -) (c₁ ⁻¹) l⁺
-- -- -- -- -- -- -- -- -- -- -- --       barbar = ap r loop ≡⟨ ap (λ - → transport (λ - → - ≡ -) - (ap r loop)) (right-inverse c₁) ⟩
-- -- -- -- -- -- -- -- -- -- -- --                transport (λ - → - ≡ -) (c₁ ∙ c₁ ⁻¹) (ap r loop) ≡⟨ transport-comp (λ - → - ≡ -) c₁ (c₁ ⁻¹) ⟩
-- -- -- -- -- -- -- -- -- -- -- --                transport (λ - → - ≡ -) (c₁ ⁻¹) (transport (λ - → - ≡ -) c₁ (ap r loop)) ≡⟨ ap (transport (λ - → - ≡ -) (c₁ ⁻¹)) bazbaz ⟩
-- -- -- -- -- -- -- -- -- -- -- --                transport (λ - → - ≡ -) (c₁ ⁻¹) l⁺ ∎
-- -- -- -- -- -- -- -- -- -- -- --       ttt : r base ≡ r base
-- -- -- -- -- -- -- -- -- -- -- --       ttt = c₁ ∙ (l⁺ ∙ c₁ ⁻¹)

-- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
-- -- -- -- -- -- -- -- -- -- -- --                     ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-comp = σ-lc (foofoo ∙ 𝕊¹-rec-comp (base , a) l⁺)

-- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    (pr₂ (base , a) , foo) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    (pr₂ (base , a) , pr₂ (loop , l)) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- --    (a , l) ∎
-- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- --      φ : Π A
-- -- -- -- -- -- -- -- -- -- -- -- --      φ = 𝕊¹-induction
-- -- -- -- -- -- -- -- -- -- -- -- --      mmm : (x : 𝕊¹) → φ x ≡ transport A (happly 𝕊¹-induction-key-lemma x) (pr₂ (r x))
-- -- -- -- -- -- -- -- -- -- -- -- --      mmm x = refl
-- -- -- -- -- -- -- -- -- -- -- -- --      kkk : (r base , ap r loop) ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- --      kkk = 𝕊¹-rec-comp (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- --      foo : transport A loop a ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- --      foo = (ap (λ - → transport A - a) (baz ⁻¹)) ∙ test
-- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- --        baz : (pr₁ (from-Σ-≡ l⁺)) ≡ loop
-- -- -- -- -- -- -- -- -- -- -- -- --        baz = ap pr₁ (fromto-Σ-≡ (loop , l))
-- -- -- -- -- -- -- -- -- -- -- -- --        test : transport A (pr₁ (from-Σ-≡ l⁺)) a ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- --        test =  pr₂ (from-Σ-≡ l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- --      type₁ : Σ y ꞉ A base , transport A loop y ≡ y
-- -- -- -- -- -- -- -- -- -- -- -- --      type₁ = (a , l)
-- -- -- -- -- -- -- -- -- -- -- -- --      type₂ : Σ w ꞉ (Σ A) ,  w ≡ w
-- -- -- -- -- -- -- -- -- -- -- -- --      type₂ = ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- --      f : (Σ y ꞉ A base ,  (base , y) ≡[ Σ A ] (base , y))
-- -- -- -- -- -- -- -- -- -- -- -- --        → (Σ y ꞉ A base , transport A loop y ≡ y)
-- -- -- -- -- -- -- -- -- -- -- -- --      f (y , 𝓁) = y , ({!!} ∙ pr₂ (from-Σ-≡ 𝓁))

-- -- -- -- -- -- -- -- -- -- -- -- -- --   TO DO: Look at JEq computation rule in MGS notes


-- -- -- -- -- -- -- -- -- -- -- -- -- --   open import Test
-- -- -- -- -- -- -- -- -- -- -- -- -- --   foo : {!!} ≡ {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- --   foo = gen-cleaned-up (base , loop) (base , loop) {!!} {!!} {!!} 𝕊¹-induction-key-≡ (to-Σ-≡ (refl , ap-id-is-id loop))


-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-comp : (𝕊¹-induction base , apd 𝕊¹-induction loop)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                     ≡[ Σ y ꞉ A base , transport A loop y ≡ y ] (a , l)
-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-comp =
-- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    (pr₂ (base , a) , foo) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    (pr₂ (base , a) , pr₂ (loop , l)) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- --    (a , l) ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- --     {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --      φ : Π A
-- -- -- -- -- -- -- -- -- -- -- -- -- --      φ = 𝕊¹-induction
-- -- -- -- -- -- -- -- -- -- -- -- -- --      mmm : (x : 𝕊¹) → φ x ≡ transport A (happly 𝕊¹-induction-key-lemma x) (pr₂ (r x))
-- -- -- -- -- -- -- -- -- -- -- -- -- --      mmm x = refl
-- -- -- -- -- -- -- -- -- -- -- -- -- --      kkk : (r base , ap r loop) ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      kkk = 𝕊¹-rec-comp (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- -- --      foo : transport A loop a ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- --      foo = (ap (λ - → transport A - a) (baz ⁻¹)) ∙ test
-- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- --        baz : (pr₁ (from-Σ-≡ l⁺)) ≡ loop
-- -- -- -- -- -- -- -- -- -- -- -- -- --        baz = ap pr₁ (fromto-Σ-≡ (loop , l))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        test : transport A (pr₁ (from-Σ-≡ l⁺)) a ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- --        test =  pr₂ (from-Σ-≡ l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      type₁ : Σ y ꞉ A base , transport A loop y ≡ y
-- -- -- -- -- -- -- -- -- -- -- -- -- --      type₁ = (a , l)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      type₂ : Σ w ꞉ (Σ A) ,  w ≡ w
-- -- -- -- -- -- -- -- -- -- -- -- -- --      type₂ = ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      f : (Σ y ꞉ A base ,  (base , y) ≡[ Σ A ] (base , y))
-- -- -- -- -- -- -- -- -- -- -- -- -- --        → (Σ y ꞉ A base , transport A loop y ≡ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- --      f (y , 𝓁) = y , ({!!} ∙ pr₂ (from-Σ-≡ 𝓁))
-- -- -- -- -- -- -- -- -- -- -- -- -- --     -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-base : 𝕊¹-induction base ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-base = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-loop : apd {!!} {!!} ≡ loop
-- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-loop = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-lemma-∼ : pr₁ ∘ r ∼ id
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-key-lemma-∼ x = {!!}



-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-base : 𝕊¹-induction base ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-on-base =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    transport A (happly 𝕊¹-induction-key-lemma base) (pr₂ (r base)) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    transport A (pr₁ (from-Σ-≡ c)) (pr₂ (r base)) ≡⟨ pr₂ (from-Σ-≡ c) ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    a ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      c : r base ≡ (base , a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      c = 𝕊¹-rec-on-base (base , a) l⁺

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-coherence₁ : happly 𝕊¹-induction-key-lemma base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                           ≡ ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   𝕊¹-induction-coherence₁ =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    happly 𝕊¹-induction-key-lemma base ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap (λ - → - base) 𝕊¹-induction-key-lemma ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap (λ - → - base) {!!} ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap (λ - → - base) (ap pr₁ big) ≡⟨ ap-ap pr₁ (λ - → - base) big ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap (λ - → (pr₁ -) base) big ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap pr₁ (ap pr₁ (pr₂ (description (𝕊¹-uniqueness-principle (base , a) l⁺)))) ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap pr₁ (ap pr₁ (𝕊¹-rec-comp (base , a) l⁺)) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap pr₁ (pr₁ (from-Σ-≡ (𝕊¹-rec-comp (base , a) l⁺))) ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    ap pr₁ (𝕊¹-rec-on-base (base , a) l⁺) ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      tttt : (pr₁ ∘ r) base ≡ base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      tttt = happly 𝕊¹-induction-key-lemma base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ϕ = ((pr₁ ∘ r) base , ap (pr₁ ∘ r) loop) ≡⟨ 𝕊¹-induction-key-≡ ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (base , loop)                        ≡⟨ e                  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          (base , ap id loop)                  ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        e = to-Σ-≡ (refl , ((ap-id-is-id loop) ⁻¹))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      big = (singletons-are-props (𝕊¹-uniqueness-principle ((pr₁ ∘ r) base) (ap (pr₁ ∘ r) loop)) ((pr₁ ∘ r) , refl) (id , (ϕ ⁻¹)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      big₁ = pr₂ (𝕊¹-uniqueness-principle {!!} {!!}) {!!} -- (r , (𝕊¹-rec-comp (base , a) l⁺))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     big₂ = pr₂ (𝕊¹-uniqueness-principle (base , a) l⁺) (r , (𝕊¹-rec-comp (base , a) l⁺))

-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  foo : (A : 𝕊¹ → 𝓤 ̇ ) (a : A base) (l : transport A loop a ≡ a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      → happly (𝕊¹-induction-key-lemma A a l) base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      ≡ pr₁ (from-Σ-≡ (𝕊¹-rec-on-base (base , a) (to-Σ-≡ (loop , l))))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  foo A a l = γ
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    l⁺ : base , a ≡ base , a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    l⁺ = to-Σ-≡ (loop , l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    r : 𝕊¹ → Σ A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    r = 𝕊¹-rec (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    κ : pr₁ ∘ r ≡ id
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    κ = 𝕊¹-induction-key-lemma A a l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    γ = happly (𝕊¹-induction-key-lemma A a l) base ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ap (λ - → - base) κ ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ap (λ - → - base) (𝕊¹-uniqueness-principle-≡ (pr₁ ∘ r) id κκ) ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              ap (λ - → - base) (ap pr₁ (singletons-are-props (𝕊¹-uniqueness-principle ((pr₁ ∘ r) base) (ap (pr₁ ∘ r) loop))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                                                         ((pr₁ ∘ r) , refl) (id , (? ⁻¹)))) ≡⟨ {!!} ⟩ -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --              {!!} ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      κκ = to-Σ-≡ (d₁ , ϕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        υ : (𝕊¹ → Σ A) → (Σ y ꞉ Σ A , y ≡ y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        υ = 𝕊¹-universal-map (Σ A)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        c : r base , ap r loop ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        c = 𝕊¹-rec-comp (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        c₁ : r base ≡ (base , a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        c₁ = pr₁ (from-Σ-≡ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        d₁ : pr₁ (r base) ≡ base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        d₁ = ap pr₁ c₁
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        ϕ = transport (λ - → - ≡ -) d₁ (ap (pr₁ ∘ r) loop)  ≡⟨ I    ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            d₁ ⁻¹ ∙ (ap (pr₁ ∘ r) loop ∙ d₁)                ≡⟨ II   ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            d₁ ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ d₁)               ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            d₁ ⁻¹ ∙ (ap pr₁ (ap r loop) ∙ (ap pr₁ c₁))      ≡⟨ III  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            d₁ ⁻¹ ∙ ap pr₁ (ap r loop ∙ c₁)                 ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            (ap pr₁ c₁) ⁻¹ ∙ ap pr₁ (ap r loop ∙ c₁)        ≡⟨ IV   ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap pr₁ (c₁ ⁻¹) ∙ ap pr₁ (ap r loop ∙ c₁)        ≡⟨ V    ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap pr₁ (c₁ ⁻¹ ∙ (ap r loop ∙ c₁))               ≡⟨ VI   ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap pr₁ (transport (λ - → - ≡ -) c₁ (ap r loop)) ≡⟨ VII  ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap pr₁ l⁺                                       ≡⟨ refl ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap pr₁ (to-Σ-≡ (loop , l))                      ≡⟨ VIII ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            loop                                            ≡⟨ IX   ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --            ap id loop                                      ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --         where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          I    = transport-along-≡-dup d₁ (ap (pr₁ ∘ r) loop)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          II   = ap (λ - → d₁ ⁻¹ ∙ (- ∙ d₁)) ((ap-ap r pr₁ loop) ⁻¹)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          III  = ap (λ - → d₁ ⁻¹ ∙ -) ((ap-∙ pr₁ (ap r loop) c₁) ⁻¹)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          IV   = ap (λ - → - ∙ ap pr₁ (ap r loop ∙ c₁)) (ap-sym pr₁ c₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          V    = (ap-∙ pr₁ (c₁ ⁻¹) (ap r loop ∙ c₁)) ⁻¹
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          VI   = ap (ap pr₁) ((transport-along-≡-dup c₁ (ap r loop)) ⁻¹)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          VII  = ap (ap pr₁) (pr₂ (from-Σ-≡ c))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          VIII = ap-pr₁-to-Σ-≡ (loop , l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --          IX   = (ap-id-is-id loop) ⁻¹


-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕊¹-induction-on-base : (A : 𝕊¹ → 𝓤 ̇ ) (a : A base) (l : transport A loop a ≡ a)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --                       → 𝕊¹-induction A a l base ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --  𝕊¹-induction-on-base A a l = {!γ!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    l⁺ : base , a ≡ base , a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    l⁺ = to-Σ-≡ (loop , l)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    r : 𝕊¹ → Σ A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    r = 𝕊¹-rec (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    κ : pr₁ ∘ 𝕊¹-rec (base , a) l⁺ ≡ id
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    κ = 𝕊¹-induction-key-lemma A a l
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c : (r base , ap r loop) ≡ ((base , a) , l⁺)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c = 𝕊¹-rec-comp (base , a) l⁺
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁ : r base ≡ base , a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁ = pr₁ (from-Σ-≡ c)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁₁ : pr₁ (r base) ≡ base
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁₁ = pr₁ (from-Σ-≡ c₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁₂ : transport A c₁₁ (pr₂ (r base)) ≡ a
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    c₁₂ = pr₂ (from-Σ-≡ c₁)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --    γ = transport A (happly κ base) (pr₂ (r base)) ≡⟨ I ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        transport A (happly κ base)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        {!!} ≡⟨ {!!} ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        transport A c₁₁ (pr₂ (r base)) ≡⟨ c₁₂ ⟩
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --        a ∎
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --      I = ap (transport A (happly κ base)) {!ap pr₂ c₁!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- \end{code}
