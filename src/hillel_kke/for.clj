(ns hillel-kke.for
  "Brute-force \"vanilla\"-Clojure solutions.

  The name of the namespace refers to the fact that the
  solution-searching in this namespace is done via a single
  for-comprehension per problem."
  (:require [clojure.set :as set]))

(defn across [vertex edge] (first (disj edge vertex)))

;; TODO: lazy lists, not sets
(defn hamiltonian-paths-from
  [vertex [vertices edges]]
  (if (= 1 (count vertices))
    #{[vertex]}
    (into #{}
          (for [out-edge (filter #(contains? % vertex) edges)
                :let [neighbor (across vertex out-edge)]
                sub-path (hamiltonian-paths-from neighbor
                                                 [(disj vertices vertex)
                                                  (disj edges out-edge)])]
            (cons vertex sub-path)))))

(defn hamiltonian-paths
  [[vertices edges :as graph]]
  (if (empty? vertices)
    #{()}
    (reduce set/union
          (for [v vertices]
            (hamiltonian-paths-from v graph)))))

(def problem-1
  (let [graph '[#{a b} #{#{a b}}]
        stations {'a (fn [me path] (= me (first path)))
                  'b (fn [me path] (= me (last path)))}
        satisfactory-knave-count? #{1 2}]
    (for [path (hamiltonian-paths graph)
          :let [assignment (into {}
                                 (map (fn [v] [v ((get stations v) v path)]))
                                 path)
                {knights true, knaves false} (group-by
                                              (fn [v]
                                                ((get stations v) v path))
                                              path)]
          :when (->> assignment
                     ;; select knaves
                     (remove val)
                     count
                     satisfactory-knave-count?)]
      {:path path
       :assignment assignment})))

(defn assignments
  "Every assignment for `stations` of `n` knaves."
  [n stations]
  ;; if requesting excessive n, then none
  (when-not (< (count stations) n)
    (if (zero? n)
      [(zipmap stations (repeat :knight))]
      (if-let [[h & t] (seq stations)]
        (lazy-cat (map #(assoc % h :knave) (assignments (dec n) t))
                  (map #(assoc % h :knight) (assignments n t)))
        [{}]))))

(def problem-2
  (let [[vertices :as graph] '[#{a b c d} #{#{a b} #{b c} #{c d} #{d a}}]
        index-of (fn [x xs]
                   (->> xs
                        (map-indexed (fn [i x] [i x]))
                        (some (fn [[i x']] (when (= x x') i)))))
        stations {'a (fn [path assignment]
                       (= :knave
                          (assignment
                           (nth path
                                (dec (index-of 'a path))
                                nil))))
                  'b (fn [path assignment]
                       ;; once again, this is the unsophisticated
                       ;; interpretation, where B-the-knave only has
                       ;; to make one lie (and not even the first
                       ;; statement has to be a lie!). But, it seems
                       ;; to work? TODO: prove manually that this
                       ;; assumption is sufficient.
                       (< (index-of 'a path)
                          (index-of 'b path)
                          (index-of 'c path)))
                  'c (fn [path assignment]
                       (->> path
                            (map assignment)
                            (partition 2 1)
                            (some (partial = [:knight :knight]))))
                  'd (fn [path assignment]
                       (let [d-index (index-of 'd path)]
                         (and (< (index-of 'a path) d-index)
                              (< (index-of 'b path) d-index))))}
        n-knaves 2]
    (for [path (hamiltonian-paths graph)
          assignment (assignments n-knaves vertices)
          :when (every? (fn [[s f]]
                          (= (= :knight (assignment s))
                             (boolean (f path assignment))))
                        stations)]
      {:path path
       :assignment assignment})))
