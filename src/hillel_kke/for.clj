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

(def problem-1
  (let [[vertices :as graph] '[#{a b} #{#{a b}}]
        stations {'a (fn [path] (= 'a (first path)))
                  'b (fn [path] (= 'b (last path)))}
        possible-knave-counts #{1 2}]
    (for [path (hamiltonian-paths graph)
          n-knaves possible-knave-counts
          assignment (assignments n-knaves vertices)
          :when (every? (fn [[s f]]
                          (= (= :knight (assignment s))
                             (boolean (f path))))
                        stations)]
      {:path path
       :assignment assignment})))

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

(def problem-3
  (let [[vertices :as graph] '[#{a b c} #{#{a b} #{b c} #{c a}}]
        index-of (fn [x xs]
                   (->> xs
                        (map-indexed (fn [i x] [i x]))
                        (some (fn [[i x']] (when (= x x') i)))))
        stations {'a (fn [path assignment raymond stinky]
                       [(not= (dec (index-of 'a path))
                              (index-of raymond path))
                        (= :knave (assignment raymond))
                        stinky])
                  'b (fn [path assignment raymond stinky]
                       [(not= (inc (index-of 'b path))
                              (index-of raymond path))
                        stinky])
                  'c (fn [path assignment raymond _]
                       (let [raymond-index (index-of raymond path)]
                         [(not (#{(inc raymond-index) (dec raymond-index)}
                                 (index-of 'c path)))]))}]
    (for [path (hamiltonian-paths graph)
          n-knaves (range 4)
          assignment (assignments n-knaves vertices)
          raymond vertices
          stinky #{true false}
          :when (every? (fn [[s f]]
                          ((if (= :knight (assignment s))
                             every?
                             not-any?)
                           boolean
                           (f path assignment raymond stinky)))
                        stations)]
      {:path path
       :assignment assignment
       :raymond raymond
       :stinky stinky})))
