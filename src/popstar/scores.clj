(ns popstar.scores
  (:require [clojure.set]))

(defn mp ([x] (do (prn x) x))
  ([x pred] (do (when (pred x) (prn x)) x)))

(defn score [n] (* 5M n n))

(defn bonus [n] (max 0 (- 2000 (* n n 20))))

(def colors #{:b :g :p :r :y })

;table [[:b :r :g ] [:p :r :r ] [:y :b :b ]]

;state [[[0 0] [0 2]] [[1 1] [1 2]] [[2 0] [2 1]]]

;point [0 1]

;color :g

(defn get-color [table state point]
  (get-in table (get-in state point)))

(defn same [table state point]
  (when-let [color (get-color table state point)]
    (loop [temp #{point} result #{point}]
      (if-let [current (first temp)]
        (let [neighbors (for [i [0 1] f [inc dec]]
                          (update-in current [i] f))
              matched (filter #(and (= color (get-color table state %)) (not (contains? result %))) neighbors)]
          (if (empty? matched)
            (recur (disj temp current) result)
            (recur (apply conj temp matched) (apply conj result matched))))
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

(defn choose-points-fn-maker [choose-fn]
  (comp
    (partial reduce #(conj %1 (choose-fn (second %2))) [])
    (partial group-by first)))

(def high-points (choose-points-fn-maker (partial apply max-key second)))

(def low-points (choose-points-fn-maker (partial apply min-key second)))

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
  (end-score [path])
  (prev-step-groups [path])
  (reusable-groups [path]))

(defrecord CachedPath [table actions total-score current-state end-score prev-step-groups reusable-groups]
  State
  (total-score [path]
    (:total-score path))
  (current-state [path]
    (:current-state path))
  (end-score [path]
    (:end-score path))
  (prev-step-groups [path]
    (:prev-step-groups path))
  (reusable-groups [path]
    (:reusable-groups path)))

(defn cached-path [table actions prev-step-groups prev-step-state]
  (let [total-score (reduce + (map (comp score count) actions))
        state (init-state table)
        current-state (reduce eliminate state actions)
        end-score (+ total-score (bonus (count (seq-from-matrix current-state))))]
    (if (empty? actions)
      (->CachedPath table actions total-score current-state end-score prev-step-groups [])
      (let [last-action (last actions)
            direct-low-points (low-points last-action)
            all-low-points (conj (mapv #(update-in % [1] dec) direct-low-points)
                             (update-in (apply min-key first direct-low-points) [0] dec)
                             (update-in (apply max-key first direct-low-points) [0] inc))
            zero-y-points (sort-by first > (filter (comp (partial = 0) second) direct-low-points))
            reusable-groups (reduce
                              #(map (comp set
                                      (partial map
                                        (fn [point] (if (> (first point) (first %2))
                                                      (update-in point [0] dec)
                                                      point)))) %1)
                              (filter
                                (partial not-any?
                                  #(some
                                     (fn [low] (and (= (first low) (first %)) (<= (second low) (second %))))
                                     all-low-points))
                                prev-step-groups) (filter #(= (count (prev-step-state (first %)))
                                                             (count (filter (comp (partial = (first %)) first) last-action)))
                                                    zero-y-points))]
        (->CachedPath table actions total-score current-state end-score prev-step-groups reusable-groups)))))

(def differences #{:lt :gt :eq :nc }) ;nc is not comparable

(defn end-differ [path1 path2]
  (let [state1 (current-state path1) state2 (current-state path2)]
    (if (= state1 state2)
      (condp = (compare (total-score path1) (total-score path2))
        1 :gt ;
        -1 :lt ;
        0 :eq ;
        :nc )
      :nc )))

(defn diff ([path1 path2]
             (diff path1 path2 :nc end-differ))
  ([path1 path2 default-value & preds]
    (cond
      (and (nil? path1) (nil? path2)) :eq ;
      (nil? path1) :lt ;
      (nil? path2) :gt ;
      :else (loop [[head tail] preds]
              (if head
                (let [result (head path1 path2)]
                  (if (contains? #{nil :nc } result)
                    (recur tail)
                    result))
                default-value)))))

(defn popstars [table]
  (loop [available #{(cached-path table [] [] nil)} saw {} wanted []]
    (if-let [head (first available)]
      (let [state (current-state head)
            all-points (points state)
            saw (set (seq-from-matrix (reusable-groups head)))
            next-point (first (filter (complement saw) all-points))
            groups (concat (reusable-groups head) (group table state all-points next-point saw))]
        (if (empty? groups)
          (if (empty? wanted)
            (recur (disj available head) saw [head (end-score head)])
            (let [score (end-score head)]
              (if (> score (wanted 1))
                (recur (disj available head) saw [head (end-score head)])
                (recur (disj available head) saw wanted))))
          (let [paths (map #(cached-path table (conj (:actions head) %) groups state) groups)
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

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y]
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))