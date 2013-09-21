(ns popstar.scores
  (:require [clojure.set]))

(def mp #(do (pr %) %))

(defn score [n] (* 5M n n))

(defn bonus [n] (max 0 (- 2000 (* n n))))

(def colors #{:b :g :p :r :y })

;table [[:b :r :g ] [:p :r :r ] [:y :b :b ]]

;state [[[0 0] [0 2]] [[1 1] [1 2]] [[2 0] [2 1]]]

;point [0 1]

;color :g

(defn get-color [table state point]
  (get-in table (get-in state point)))

(defn same [table state point]
  (when-let [color (get-color table state point)]
    (loop [temp #{point} result #{}]
      (if-let [current (first temp)]
        (let [neighbors (for [i [0 1] f [inc dec]]
                          (update-in current [i] f))
              matched (set (filter #(and (= color (get-color table state %)) (not (contains? result %))) neighbors))]
          (recur (disj (clojure.set/union temp matched) current) (conj result current)))
        result))))

(defn init-state [table]
  (let [x (count table)
        inner-seq (fn [ix iy] (for [vy (range iy)]
                                [ix vy]))]
    (vec (for [vx (range x)]
           (vec (inner-seq vx (count (nth table vx))))))))

(def init-state (memoize init-state))

(defn points [state]
  (when (not-empty state)
    (loop [current [0 0] result []]
      (cond
        (and (nil? (get-in state current)) (= 0 (second current))) result
        (nil? (get-in state current)) (recur [(inc (first current)) 0] result)
        :else (recur (update-in current [1] inc) (conj result current))))))

(def seq-from-matrix (partial apply concat))

(defn group
  ([table]
    (let [state (init-state table)]
      (group table state state)))
  ([table state]
    (group table state (points state)))
  ([table state all-points]
    (when (not-empty state)
      (group table state all-points [0 0] #{})))
  ([table state all-points current saw]
    (when current
      (lazy-seq
        (let [same-points (same table state current)
              new-saw (clojure.set/union saw same-points)
              next-point (first (filter (complement new-saw) all-points))]
          (if (= #{current} same-points)
            (group table state all-points next-point new-saw)
            (cons same-points (group table state all-points next-point new-saw))))))))

(def end? (comp boolean not-empty group))

(defn eliminate [state agroup]
  (filterv not-empty
    (mapv (partial filterv (complement nil?))
      (reduce #(assoc-in %1 %2 nil) state agroup))))

(defprotocol State
  (total-score [path])
  (current-state [path])
  (end-score [path]))

(defrecord Path [table actions]
  State
  (total-score [path]
    (reduce + (map (comp score count) (:actions path))))
  (current-state [path]
    (let [state (init-state (:table path))]
      (reduce eliminate state (:actions path))))
  (end-score [path]
    (let [state (current-state path)]
      (+ (total-score path) (bonus (count state))))))

;(def total-score (memoize total-score))
;(def current-state (memoize current-state))
;(def end-score (memoize end-score))

(def differences #{:lt :gt :eq :nc }) ;nc is not comparable

(defn diff [path1 path2]
  (cond
    (and (nil? path1) (nil? path2)) :eq ;
    (nil? path1) :lt ;
    (nil? path2) :gt ;
    :else (let [score1 (total-score path1) score2 (total-score path2)
                state1 (current-state path1) state2 (current-state path2)]
            (if (= state1 state2)
              (condp = (compare score1 score2)
                1 :gt ;
                -1 :lt ;
                0 :eq ;
                :nc )
              :nc ))))

(defn popstars [table]
  (loop [available #{(->Path table [])} saw {} wanted []]
    (if-let [head (first available)]
      (let [groups (group table (current-state head))]
        (if (empty? groups)
          (if (empty? wanted)
            (recur (disj available head) saw [head (end-score head)])
            (let [score (end-score head)]
              (if (> score (wanted 1))
                (recur (disj available head) saw [head (end-score head)])
                (recur (disj available head) saw wanted))))
          (let [paths (map #(->Path table (conj (:actions head) %)) groups)
                new-saw (loop [init paths result-map {}]
                          (if (empty? init)
                            result-map
                            (let [path (first init)
                                  state (current-state path)
                                  difference (cond
                                               (contains? result-map state) (diff path (result-map state))
                                               (contains? saw state) (diff path (saw state))
                                               :else :nc )]
                              (if (contains? #{:gt :nc } difference)
                                (recur (rest init) (conj result-map [state path]))
                                (recur (rest init) result-map)))))]
            (if (empty? new-saw)
              (recur (disj available head) saw wanted)
              (recur (apply conj (disj available head) (vals new-saw)) (merge saw new-saw) wanted)))))
      wanted)))