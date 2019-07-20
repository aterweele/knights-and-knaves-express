(ns hillel-kke.logic
  (:refer-clojure :exclude [==])
  (:require clojure.core.logic
            [clojure.string :as str]))

(defn- replace-last
  [s suffix]
  (str (subs s 0 (dec (count s))) suffix))

(use ['clojure.core.logic
      :rename (merge (into {}
                           (comp (map (juxt identity str))
                                 (map (fn [[sym s]] [sym (symbol (replace-last s \ᵉ))])))
                           '[conde defne fne matche])
                     (into {}
                           (comp (map (juxt identity str))
                                 ;; TODO: also all that end in a or u ?
                                 (filter (comp #(str/ends-with? % "o") second))
                                 (map (fn [[sym s]]
                                        [sym (symbol (replace-last s \°))])))
                           (keys (ns-publics 'clojure.core.logic))))])

(defnᵉ hamiltonian-path [graph path]
  ([[[] _]
    nil])
  ([[[v] _]
    [v]])
  ([[V E]
    p]
   (fresh [v₁ v₂ p' V']
     (first° p' v₁)
     (cons° v₂ p' p)
     (condᵉ
      [(member° [v₁ v₂] E)]
      [(member° [v₂ v₁] E)])
     (rember° v₂ V V')
     (hamiltonian-path [V' E] p'))))
