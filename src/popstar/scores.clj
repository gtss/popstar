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

(defn inner-seq [ix iy]
  (for [vy (range iy)]
    [ix vy]))

(defn matrix [count-vec inner-fn outer-fn]
  (outer-fn (for [vx (range (count count-vec))]
              (inner-fn (inner-seq vx (count-vec vx))))))

(def ^:dynamic dynamic-matrix matrix)

(defn init-state [table]
  (dynamic-matrix (mapv count table) vec vec))

(def seq-from-matrix (partial apply concat))

(defn line-group
  ([table]
    (let [state (init-state table)]
      (line-group table state)))
  ([table state]
    (line-group table state (init-state state)))
  ([table state points-matrix]
    (reduce #(apply line-group table state %2 %1) [{} {}] points-matrix))
  ([table state some-points map-pi map-ii]
    (loop [i (inc (apply max 0 (vals map-pi))) sp some-points mpi map-pi mii map-ii]
      (if-let [head (first sp)]
        (let [x0 (= 0 (head 0)) y0 (= 0 (head 1))]
          (cond
            (and (not x0) (not y0)) (let [p1 (update-in head [1] dec)
                                          p2 (update-in head [0] dec)
                                          hc (get-color table state head)
                                          p1c (get-color table state p1)
                                          p2c (get-color table state p2)]
                                      (cond
                                        (= hc p1c p2c) (let [p1i (mpi p1)
                                                             p2i (mpi p2)
                                                             mini (min (mii p1i) (mii p2i))]
                                                         (recur i (rest sp) (conj mpi [head (mpi p1)]) (conj mii [p1i mini] [p2i mini])))
                                        (= hc p1c) (recur i (rest sp) (conj mpi [head (mpi p1)]) mii)
                                        (= hc p2c) (recur i (rest sp) (conj mpi [head (mpi p2)]) mii)
                                        :else (recur (inc i) (rest sp) (conj mpi [head i]) (conj mii [i i]))))
            (and x0 y0) (recur (inc i) (rest sp) (conj mpi [head i]) (conj mii [i i]))
            :else (let [p (if x0 (update-in head [1] dec) (update-in head [0] dec))
                        hc (get-color table state head)
                        pc (get-color table state p)]
                    (if (= hc pc)
                      (recur i (rest sp) (conj mpi [head (mpi p)]) mii)
                      (recur (inc i) (rest sp) (conj mpi [head i]) (conj mii [i i]))))))
        [mpi mii]))))

(def count-pred (comp (partial < 1) count))

(defn group-from-line-group [[mpi mii]]
  (filter count-pred (vals (group-by (comp mii mpi) (keys mpi)))))

(def group (comp group-from-line-group line-group))

(def partial-filterv-complement-nil? (partial filterv (complement nil?)))

(def assoc-in-nil #(assoc-in %1 %2 nil))

(defn eliminate [state agroup]
  (filterv not-empty
    (mapv partial-filterv-complement-nil?
      (reduce assoc-in-nil state agroup))))

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
  (+ (total-score path) (-> path current-state-seq count bonus)))

(defn merge-info-to-vector-from-a-seq [vector-c2 aseq]
  (let [n (count aseq)]
    (if (= 1 n)
      (update-in vector-c2 [1] inc)
      (update-in vector-c2 [0] (partial + (score n))))))

(defn simple-max-estimation [path]
  (let [gs (vals (group-by (partial get-color (:table path)) (current-state-seq path)))
        tmp (reduce merge-info-to-vector-from-a-seq [0 0] gs)]
    (+ (total-score path) (tmp 0) (bonus (tmp 1)))))

(def comp-score-count (comp score count))

(defn simple-min-estimation [path]
  (let [gs (groups path)
        all-n (count (current-state-seq path))
        cgs (count gs)
        parts (+ cgs (- all-n (count (seq-from-matrix gs))))]
    (apply + (total-score path) (bonus (- parts cgs)) (map comp-score-count gs))))

(defn path-groups [path]
  (group (:table path) (current-state path)))

(defn path-total-score [path]
  (reduce + (map comp-score-count (actions path))))

(defn path-current-state-seq [path]
  (seq-from-matrix (current-state path)))

(defn empty-actions [_] [])

(defn zero-score [_] 0)

(defn path-init-state [path]
  (init-state (:table path)))

(defn first-lazy-cached-path [table]
  (->LazyCachedPath
    table
    (memoize path-groups)
    empty-actions
    zero-score
    (memoize path-init-state)
    (memoize path-current-state-seq)
    (memoize simple-max-estimation)
    (memoize simple-min-estimation)))

(defn next-lazy-cached-path [prev-path last-action]
  (let [actions-fn (memoize (fn [self] (conj (actions prev-path) last-action)))
        current-state-fn (memoize (fn [self] (eliminate (current-state prev-path) last-action)))]
    (->LazyCachedPath
      (:table prev-path)
      (memoize path-groups)
      actions-fn
      (memoize path-total-score)
      current-state-fn
      (memoize path-current-state-seq)
      (memoize simple-max-estimation)
      (memoize simple-min-estimation))))

(def differences #{:lt :gt :eq :nc }) ;nc is not comparable

(defn score-differ [path1 path2]
  (condp = (compare (total-score path1) (total-score path2))
    1 :gt ;
    -1 :lt ;
    0 :eq ;
    :nc ))

(defn diff ([path1 path2]
             (diff path1 path2 :nc score-differ))
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

(def path-comparator #(if (= %1 %2)
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
                                                -1))))))))

(defn popstars [table]
  (binding [dynamic-matrix (memoize matrix)]
    (loop [available (sorted-set-by path-comparator (first-lazy-cached-path table))
           saw {} estimation 0 wanted []]
      (if-let [head (first available)]
        (if-let [head-groups (not-empty (groups head))]
          (let [paths (map #(next-lazy-cached-path head %) head-groups)
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
        wanted))))

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y]
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))