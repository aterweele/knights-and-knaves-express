(ns hillel-kke.logic
  (:refer-clojure :exclude [==])
  (:require clojure.core.logic
            [clojure.core.logic.fd :as fd]
            [clojure.string :as str]))

(defn- replace-last
  [s suffix]
  (str (subs s 0 (dec (count s))) suffix))

;; Per Byrd's thesis: "By our convention, names of relations end with
;; a superscript o — for example substᵒ, which is entered as
;; `substo`."  Fix this concession to ASCII; use Unicode superscripts.
(use ['clojure.core.logic
      :rename (merge (into {}
                           (for [s ["cond" "defn" "fn" "match"]
                                 [original new] [[\a \ᵃ] [\e \ᵉ] [\u \ᵘ]]]
                             [(symbol (str s original)) (symbol (str s new))]))
                     (into {}
                           (comp (map (juxt identity str))
                                 (filter (comp #(str/ends-with? % "o") second))
                                 (map (fn [[sym s]]
                                        [sym (symbol (replace-last s \ᵒ))])))
                           (keys (ns-publics 'clojure.core.logic)))
                     {'!= '≠})])

(defnᵉ hamiltonian-pathᵒ [graph path]
  ([[[] _]
    nil])
  ([[[v] _]
    [v]])
  ([[V E]
    p]
   (fresh [v₁ v₂ p' V']
     (firstᵒ p' v₁)
     (consᵒ v₂ p' p)
     (condᵉ
      ;; I think if I used remberᵒ here, then the function would work
      ;; "backwards".
      [(memberᵒ [v₁ v₂] E)]
      [(memberᵒ [v₂ v₁] E)])
     (remberᵒ v₂ V V')
     (hamiltonian-pathᵒ [V' E] p'))))

(defnᵉ lastᵒ [l x]
  ([[] _] fail)
  ([[x] x] succeed)
  ([l x]
   (fresh [l']
     (restᵒ l l')
     (lastᵒ l' x))))

(defnᵉ n-knavesᵒ [n roles]
  ([0 []])
  ([n roles]
   (fresh [role roles']
     (consᵒ role roles' roles)
     (condᵉ
      [(== role :knave)
       (fresh [n-1]
         (fd/+ n-1 1 n)
         (n-knavesᵒ n-1 roles'))]
      [(== role :knight)
       (n-knavesᵒ n roles')]))))

;; with many thanks to
;; https://blog.taylorwood.io/2018/05/10/clojure-logic.html for the
;; "programmatically creating lvars" strategy.
(defn express
  "A goal giving the solution to a Knights and Knaves Express
  problem. At least, for problems 1 and 2, where stations' claims are
  about concrete other stations. Problem 3 has claims about an
  abstract third station, and so doesn't fit into this mold."
  [{:keys [graph stations knaves-domain]}]
  (let [station->role (zipmap (keys stations) (repeatedly lvar))
        roles (vals station->role)]
    (fnᵉ
     [path assignment]
     ([path assignment]
      (hamiltonian-pathᵒ graph path)
      (and* (map (fn [[station role]]
                   (let [{:keys [knight knave]} (stations station)
                         knight-goal (knight station path station->role)
                         knave-goal (knave station path station->role)]
                     (condᵉ
                      [(== role :knight) knight-goal]
                      [(== role :knave) knave-goal])))
                 station->role))
      (fresh [n-knaves]
        (fd/in n-knaves knaves-domain)
        (n-knavesᵒ n-knaves roles))
      (== assignment station->role)))))

(defnᵉ prefixᵒ [l prefix]
  ([l []])
  ([l prefix]
   (fresh [x l' prefix']
     (consᵒ x prefix' prefix)
     (consᵒ x l' l)
     (prefixᵒ l' prefix'))))

(defnᵉ subseqᵒ [l sub]
  ([l []])
  ([l sub]
   (condᵉ
    [(fresh [l']
       (restᵒ l l')
       (subseqᵒ l' sub))]
    [(prefixᵒ l sub)])))

(defnᵉ beforeᵒ
  "`x` before `y` in `l`"
  [x y l]
  ([x y l]
   (fresh [l']
     (condᵉ
      [(consᵒ x l' l)
       (memberᵒ y l')]
      [(restᵒ l l')
       (beforeᵒ x y l')]))))

(defn role
  "Yields a goal for a station having a role under `path` (an lvar)
  and `station->role`, the lvar for the role of a given station."
  [path station->role]
  (let [station-roles (seq station->role)]
    (fnᵉ
     [station role]
     ([s r] (memberᵒ [s r] station-roles)))))

;;; problem definitions

(def problem-1
  {:graph '[[a b] [[a b]]]
   :stations
   {'a {:knight (fn [me path _] (firstᵒ path me))
        :knave
        (fn [me path _]
          (fresh [first]
            (firstᵒ path first)
            (≠ first me)))}
    'b {:knight (fn [me path _] (lastᵒ path me))
        :knave
        (fn [me path _]
          (fresh [last]
            (lastᵒ path last)
            (≠ last me)))}}
   :knaves-domain (fd/interval 1 2)})

(def problem-2
  {:graph '[[a b c d] [[a b] [b c] [c d] [d a]]]
   :stations
   {'a {:knight
        (fn [me path station->role]
          (let [roleᵒ (role path station->role)]
            (fresh [the-knave-before]
              (subseqᵒ path [the-knave-before me])
              (roleᵒ the-knave-before :knave))))
        :knave
        (fn [me path station->role]
          (let [roleᵒ (role path station->role)]
            (condᵉ
             [(fresh [the-knight-before]
                (subseqᵒ path [the-knight-before me])
                (roleᵒ the-knight-before :knight))]
             [(firstᵒ path me)])))}
    ;; for b's second statement, I interpret it as logical conjunction
    ;; with the first statement, but there is a more sophisticated
    ;; interpretation. Namely, that if b is a knave, then their first
    ;; statement MUST be false, because if it were true, then they
    ;; wouldn't be able to claim it in isolation.
    'b {:knight
        (fn [me path _]
          (all
           (beforeᵒ me 'c path)
           (beforeᵒ 'a me path)))
        :knave
        (fn [me path _]
          ;; sophisticated interpretation:
          #_(beforeᵒ 'c me path)
          ;; unsophisticated interpretation:
          (condᵉ
           [(beforeᵒ 'c me path)]
           [(beforeᵒ me 'a path)]))}
    'c {:knight
        (fn [_ path station->role]
          (let [roleᵒ (role path station->role)]
            (fresh [knight₁ knight₂]
              (subseqᵒ path [knight₁ knight₂])
              (roleᵒ knight₁ :knight)
              (roleᵒ knight₂ :knight))))
        :knave
        (fn [_ path station->role]
          ;; here I encode that the only ways for 2 knights to not be
          ;; adjacent in this problem is to have a subsequence that is
          ;; kight-knave-kight or knight-knave-knave-knight. This
          ;; exploits some global knowledge of the problem - the length
          ;; of the path - more than the other `:knight`/`:knave`
          ;; functions do. So, I consider it a bit of a cheap shot.
          (let [roleᵒ (role path station->role)]
            (condᵉ
             [(fresh [station₁ station₂ station₃]
                (roleᵒ station₁ :knight)
                (roleᵒ station₂ :knave)
                (roleᵒ station₃ :knight)
                (subseqᵒ path [station₁ station₂ station₃]))]
             [(fresh [station₁ station₂ station₃ station₄]
                (roleᵒ station₁ :knight)
                (roleᵒ station₂ :knave)
                (roleᵒ station₃ :knave)
                (roleᵒ station₄ :knight)
                (subseqᵒ path [station₁ station₂ station₃ station₄]))])))}
    'd {:knight
        (fn [me path _]
          (all
           (beforeᵒ 'a me path)
           (beforeᵒ 'b me path)))
        :knave
        (fn [me path _]
          (condᵉ
           [(beforeᵒ me 'a path)]
           [(beforeᵒ me 'b path)]))}}
   :knaves-domain (fd/domain 2)})

#_
(def problem-3
  {:graph '[[a b c] [[a b] [b c] [c a]]]
   :stations
   {'a {:knight
        (fn [me path])}}
   :knaves-domain (fd/interval 0 3)})

(def problem-3
  (let [[stations edges :as graph] '[[a b c] [[a b] [b c] [c a]]]
        ;; a, b, and c are lvars for the roles of those stations.
        {:syms [a b c] :as station->role} (zipmap stations (repeatedly lvar))
        roles (vals station->role)
        ;; this is a bit of a hack.
        path-external (lvar)
        roleᵒ (role path-external station->role)
        ]
    (fnᵉ
     [path assignment raymond smells-bad]
     ([path assignment raymond smells-bad]
      (== path-external path)
      (hamiltonian-pathᵒ graph path)
      ;; A
      (condᵉ
       [(== a :knight)
        ;; "Don't put Raymond right before me"
        (condᵉ
         [(firstᵒ path 'a)]
         [(fresh [not-raymond]
            (subseqᵒ path [not-raymond 'a])
            (≠ raymond not-raymond))])
        ;; "He's ... a Knave"
        (roleᵒ raymond :knave)
        ;; "He smells bad"
        (== smells-bad true)]
       [(== a :knave)
        ;; DO put Raymond before A.
        (subseqᵒ path [raymond 'a])
        ;; Raymond is not a knave.
        (roleᵒ raymond :knight)
        ;; Nor is he smelly.
        (== smells-bad false)])
      ;; B
      (condᵉ
       [(== b :knight)
        ;; "Don't put Raymond right after me."
        (condᵉ
         [(lastᵒ path 'b)]
         [(fresh [not-raymond]
            (subseqᵒ path ['b not-raymond])
            (≠ raymond not-raymond))])
        ;; "He smells bad"
        (== smells-bad true)]
       [(== b :knave)
        ;; DO put Raymond after B
        (subseqᵒ path ['b raymond])
        ;; Raymond does not smell bad.
        (== smells-bad false)])
      ;; C
      (condᵉ
       [(== c :knight)
        ;; "Don't put Raymond right before or right after me."
        (condᵉ
         [(fresh [before after]
            (subseqᵒ path [before 'c after])
            (≠ before raymond)
            (≠ after raymond))]
         [(firstᵒ path 'c)]
         [(lastᵒ path 'c)])]
       [(== c :knave)
        ;; my interpretation here is that Raymond must be either
        ;; before or after.
        (condᵉ
         [(fresh [after]
            (subseqᵒ path ['c after])
            (== raymond after))]
         [(fresh [before]
            (subseqᵒ path [before 'c])
            (== raymond before))])])
      (== assignment station->role)))))
