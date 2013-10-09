(ns popstar.scores
  (:require [clojure.set]))

(defn mp ([x] (do (prn x) x))
  ([x pred] (do (when (pred x) (prn x)) x)))

(def score (vec (for [n (range 101)] (* 5 n n))))

(def bonus-vec (vec (for [n (range 10)] (- 2000 (* 20 n n)))))

(defn bonus [n] (if (>= n 10) 0 (bonus-vec n)))

(def colors #{:b :g :p :r :y })

;table [[:b :r :g ] [:p :r :r ] [:y :b :b ]]

;state [[[0 0] [0 2]] [[1 1] [1 2]] [[2 0] [2 1]]]

;point [0 1]

;color :g

(defn get-color
  ([table states point]
    (get-in table (get-in states point)))
  ([table state]
    (get-in table state)))

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

(defn matrix [src inner-fn outer-fn]
  (let [x (count src)
        inner-seq (fn [ix iy] (for [vy (range iy)]
                                [ix vy]))]
    (outer-fn (for [vx (range x)]
                (inner-fn (inner-seq vx (count (nth src vx))))))))

(defn init-state [table]
  (matrix table vec vec))

(defn points [state]
  (matrix state set (partial apply clojure.set/union)))

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
      (group table state)))
  ([table state]
    (group table state (points state)))
  ([table state all-points]
    (when (not-empty state)
      (group table state all-points [0 0])))
  ([table state all-points current]
    (when current
      (lazy-seq
        (let [same-points (same table state current)
              new-points (clojure.set/difference all-points same-points)
              next-point (first new-points)]
          (if (= #{current} same-points)
            (group table state new-points next-point)
            (cons same-points (group table state new-points next-point))))))))

(def end? (comp boolean not-empty group))

(defn eliminate [state agroup]
  (filterv not-empty
    (mapv (partial filterv (complement nil?))
      (reduce #(assoc-in %1 %2 nil) state agroup))))

(defprotocol State
  (groups [path])
  (actions [path])
  (total-score [path])
  (current-state [path])
  (current-state-seq [path])
  (max-estimation [path])
  (min-estimation [path]))

(defrecord LazyCachedPath [table groups actions total-score current-state current-state-seq max-estimation min-estimation]
  State
  (groups [path]
    ((:groups path) path))
  (actions [path]
    ((:actions path) path))
  (total-score [path]
    ((:total-score path) path))
  (current-state [path]
    ((:current-state path) path))
  (current-state-seq [path]
    ((:current-state-seq path) path))
  (max-estimation [path]
    ((:max-estimation path) path))
  (min-estimation [path]
    ((:min-estimation path) path)))

(defn end-score [path]
  (+ (total-score path)
    ((comp bonus count seq-from-matrix current-state) path)))

(defn simple-max-estimation [path]
  (let [gs (vals (group-by (partial get-color (:table path)) (current-state-seq path)))
        tmp (reduce #(if (= 1 (count %2)) (update-in %1 [1] inc) (update-in %1 [0] (partial + (score (count %2))))) [0 0] gs)]
    (+ (total-score path) (tmp 0) (bonus (tmp 1)))))

(defn simple-min-estimation [path]
  (let [gs (groups path)
        all-n (count (current-state-seq path))
        parts (+ (count gs) (- all-n (count (seq-from-matrix gs))))]
    (apply + (total-score path) (bonus (- parts (count gs))) (map (comp score count) gs))))

(defn lazy-cached-path [table prev-path last-action]
  (if prev-path
    (let [groups-fn (memoize (fn [self] (group table (current-state self))))
          actions-fn (memoize (fn [self] (conj (actions prev-path) last-action)))
          total-score-fn (memoize (fn [self] (reduce + (map (comp score count) (actions self)))))
          current-state-fn (memoize (fn [self] (eliminate (current-state prev-path) last-action)))
          current-state-seq-fn (memoize (fn [self] (seq-from-matrix (current-state self))))]
      (->LazyCachedPath table groups-fn actions-fn total-score-fn current-state-fn current-state-seq-fn (memoize simple-max-estimation) (memoize simple-min-estimation)))
    (let [groups-fn (memoize (fn [self] (group table (current-state self))))
          actions-fn (fn [_] [])
          total-score-fn (fn [_] 0)
          current-state-fn (memoize (comp init-state :table ))
          current-state-seq-fn (memoize (fn [self] (seq-from-matrix (current-state self))))]
      (->LazyCachedPath table groups-fn actions-fn total-score-fn current-state-fn current-state-seq-fn (memoize simple-max-estimation) (memoize simple-min-estimation)))))

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
      :else (loop [[head & tail] preds]
              (if head
                (let [result (head path1 path2)]
                  (if (contains? #{nil :nc } result)
                    (recur tail)
                    result))
                default-value)))))

(defn popstars [table]
  (loop [available (sorted-set-by #(if (= %1 %2)
                                     0
                                     (let [me1 (min-estimation %1)
                                           me2 (min-estimation %2)]
                                       (cond
                                         (> (- me1) (- me2)) 1
                                         (< (- me1) (- me2)) -1
                                         :else (let [ts1 (total-score %1)
                                                     ts2 (total-score %2)]
                                                 (cond
                                                   (< ts1 ts2) 1
                                                   (> ts1 ts2) -1
                                                   :else (let [cg1 (count (groups %1))
                                                               cg2 (count (groups %2))]
                                                           (if (> cg1 cg2) 1
                                                             -1))))))) (lazy-cached-path table nil nil))
         saw {} estimation 0 wanted []]
    (if-let [head (first available)]
      (if-let [head-groups (not-empty (groups head))]
        (let [paths (map #(lazy-cached-path table head %) head-groups)
              new-saw (loop [init paths result-map {}]
                        (if (empty? init)
                          result-map
                          (let [path (first init)
                                state (current-state path)
                                difference (cond
                                             (contains? result-map state) (diff path (result-map state))
                                             (contains? saw state) (diff path (saw state))
                                             (> estimation (max-estimation head)) :lt ;
                                             :else :nc )]
                            (if (contains? #{:gt :nc } difference)
                              (recur (rest init) (conj result-map [state path]))
                              (recur (rest init) result-map)))))
              new-estimation (max estimation (min-estimation head))]
          (if (empty? new-saw)
            (recur (disj available head) saw new-estimation wanted)
            (recur (apply conj (disj available head) (vals new-saw)) (merge saw new-saw) new-estimation wanted)))
        (let [score (end-score head)]
          (cond (empty? wanted) (recur (disj available head) saw (max estimation score) [head score])
            (> score (wanted 1)) (recur (disj available head) saw (max estimation score) [head score])
            :else (recur (disj available head) saw estimation wanted))))
      wanted)))

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y]
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))