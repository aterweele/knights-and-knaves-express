(ns hillel-kke.for
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
        knight? (fn [assignment station] (= :knight (assignment station)))
        stations {'a (fn [me path assignment]
                       (let [me-knight (knight? assignment me)
                             me-assignment (assignment me)
                             before-me-assignment
                             (->> (index-of me path)
                                  dec
                                  (get path)
                                  assignment)]
                         (or (and me-knight
                                  (= before-me-assignment :knave))
                             (and (not me-knight)
                                  (not= before-me-assignment :knave)))))
                  'b (fn [me path assignment]
                       (let [me-knight (knight? assignment me)
                             me-index (index-of me path)
                             a-b (< (index-of 'a path) me-index)
                             b-c (< me-index (index-of 'c path))]
                         (or (and me-knight a-b b-c)
                             (and (not me-knight)
                                  ;; assume every statement leaves the
                                  ;; world consistent. Then, it is
                                  ;; only necessary for B's first
                                  ;; statement to be false.
                                  #_(not a-b)
                                  ;; per "knaves always lie", both
                                  ;; statements must be false.
                                  (not a-b) (not b-c)))))
                  'c (fn [me path assignment]
                       (= (knight? assignment me)
                          (->> path
                               (map assignment)
                               (partition 2 1)
                               (some (partial = [:knight :knight]))
                               boolean)))
                  'd (fn [me path assignment]
                       (= (knight? assignment me)
                          (let [me-index (index-of me path)]
                            (and (< (index-of 'a path) me-index)
                                 (< (index-of 'b path) me-index)))))}
        n-knaves 2]
    (for [path (hamiltonian-paths graph)
          assignment (assignments n-knaves vertices)
          :when (every? (fn [[s f]] (f s path assignment)) stations)]
      {:path path
       :assignment assignment})))
