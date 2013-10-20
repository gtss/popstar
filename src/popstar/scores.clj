(ns popstar.scores
  (:require [clojure.set]))

(defn mp ([x] (do (prn x) x))
  ([x pred] (do (when (pred x) (prn x)) x)))

(def score (vec (concat [0 0] (for [n (range 2 101)] (* 5 n n)))))

(def bonus-vec (vec (for [n (range 10)] (- 2000 (* 20 n n)))))

(defn bonus [n] (if (>= n 10) 0 (nth bonus-vec n)))

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

(defn inner-vec [ix iy]
  (mapv (partial vector ix) (range iy)))

(def cached-index-lines
  (vec (for [x (range 10)]
         (vec (for [length (range 11)]
                (inner-vec x length))))))

(def get-line (comp (partial get-in cached-index-lines) vector))

(def map-count (partial map count))

(def index-matrix (comp vec (partial map-indexed get-line) map-count))

(def +seq (partial apply +))

(def count-matrix (comp +seq map-count))

(defn line-group
  ([table]
    (let [state (index-matrix table)]
      (line-group table state)))
  ([table state]
    (line-group table state (index-matrix state)))
  ([table state points-matrix]
    (reduce #(apply line-group table state %2 %1) [{} {}] points-matrix))
  ([table state some-points map-pi map-ii]
    (loop [i (inc (apply max 0 (vals map-pi))) j 0 lastp nil lastc nil lasti 0 mpi map-pi mii map-ii]
      (if-let [head (get some-points j)]
        (let [x0 (= 0 (nth head 0)) y0 (= 0 (nth head 1)) hc (get-color table state head) j1 (inc j)]
          (cond
            (and (not x0) (not y0)) (let [p2 (update-in head [0] dec)
                                          p2c (get-color table state p2)]
                                      (cond
                                        (= hc lastc p2c) (let [p2i (mpi p2)
                                                               lastii (get mii lasti lasti)
                                                               p2ii (get mii p2i p2i)
                                                               new-mii (cond (> lastii p2ii) (conj mii [lasti p2ii])
                                                                         (< lastii p2ii) (conj mii [p2i lastii])
                                                                         :else mii)]
                                                           (recur i j1 head hc lasti (conj mpi [head lasti]) new-mii))
                                        (= hc lastc) (recur i j1 head hc lasti (conj mpi [head lasti]) mii)
                                        (= hc p2c) (let [p2i (mpi p2)] (recur i j1 head hc (long p2i) (conj mpi [head p2i]) mii))
                                        :else (recur (inc i) j1 head hc (long i) (conj mpi [head i]) mii)))
            (and x0 (not y0)) (if (= hc lastc)
                                (recur i j1 head hc lasti (conj mpi [head lasti]) mii)
                                (recur (inc i) j1 head hc (long i) (conj mpi [head i]) mii))
            (and (not x0) y0) (let [p (update-in head [0] dec)
                                    pc (get-color table state p)]
                                (if (= hc pc)
                                  (let [pi (mpi p)] (recur i j1 head hc (long pi) (conj mpi [head pi]) mii))
                                  (recur (inc i) j1 head hc (long i) (conj mpi [head i]) mii)))
            :else (recur (inc i) j1 head hc (long i) (conj mpi [head i]) mii)))
        [mpi mii]))))

(def count-pred (comp (partial < 1) count))

(defn group-from-line-group [[mpi mii]]
  (filter count-pred (vals (group-by #(let [i (mpi %)] (get mii i i)) (keys mpi)))))

(def group (comp group-from-line-group line-group))

(def ^:dynamic dynamic-group group)

(def partial-filterv-complement-nil? (partial filterv (complement nil?)))

(def assoc-in-nil #(assoc-in %1 %2 nil))

(defn eliminate [state agroup]
  (filterv not-empty
    (mapv partial-filterv-complement-nil?
      (reduce assoc-in-nil state agroup))))

(defprotocol Path
  (groups [path])
  (actions [path])
  (^long total-score [path])
  (current-state [path])
  (max-estimation [path])
  (^long min-estimation [path]))

(defrecord LazyCachedPath [table groups actions total-score current-state max-estimation min-estimation]
  Path
  (groups [path]
    ((:groups path) path))
  (actions [path]
    ((:actions path) path))
  (total-score [path]
    ((:total-score path) path))
  (current-state [path]
    ((:current-state path) path))
  (max-estimation [path]
    ((:max-estimation path) path))
  (min-estimation [path]
    ((:min-estimation path) path)))

(defn end-score
  (^long [path]
    (+ (total-score path) (-> path current-state count-matrix bonus))))

(defn merge-info-to-vector-from-a-seq [vector-c2 aseq]
  (let [n (count aseq)]
    (if (= 1 n)
      (update-in vector-c2 [1] inc)
      (update-in vector-c2 [0] (partial + (score n))))))

(defn simple-max-estimation [path]
  (let [gs (vals (apply merge-with concat
                   (map (partial group-by (partial get-color (:table path))) (current-state path))))
        tmp (reduce merge-info-to-vector-from-a-seq [0 0] gs)]
    (+ (total-score path) (nth tmp 0) (bonus (nth tmp 1)))))

(def comp-score-count (comp score count))

(defn simple-min-estimation [path]
  (let [gs (groups path)
        all-n (count-matrix (current-state path))]
    (+seq (total-score path) (bonus (- all-n (count-matrix gs))) (map comp-score-count gs))))

(defn path-groups [path]
  (dynamic-group (:table path) (current-state path)))

(defn empty-actions [_] [])

(defn zero-score [_] 0)

(defn path-init-state [path]
  (index-matrix (:table path)))

(defn first-lazy-cached-path [table]
  (->LazyCachedPath
    table
    (memoize path-groups)
    empty-actions
    zero-score
    (memoize path-init-state)
    (memoize simple-max-estimation)
    (memoize simple-min-estimation)))

(defn next-lazy-cached-path [prev-path last-action]
  (let [actions-fn (memoize (fn [self] (conj (actions prev-path) last-action)))
        path-total-score-fn (memoize (fn [_] (+ (total-score prev-path) (comp-score-count last-action))))
        current-state-fn (memoize (fn [self] (eliminate (current-state prev-path) last-action)))]
    (->LazyCachedPath
      (:table prev-path)
      (memoize path-groups)
      actions-fn
      path-total-score-fn
      current-state-fn
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
  (binding [dynamic-group (memoize group)]
    (loop [available (sorted-set-by path-comparator (first-lazy-cached-path table))
           saw {} estimation 0 wanted nil]
      (if-let [head (first available)]
        (if-let [head-groups (not-empty (groups head))]
          (let [paths (map #(next-lazy-cached-path head %) head-groups)
                new-saw (reduce
                          (fn [result-map path]
                            (let [state (current-state path)
                                  difference (cond
                                               (contains? result-map state) (diff path (result-map state))
                                               (contains? saw state) (diff path (saw state))
                                               (> estimation (max-estimation head)) :lt ;
                                               :else :nc )]
                              (if (contains? #{:gt :nc } difference)
                                (conj result-map [state path])
                                result-map))) {} paths)
                new-estimation (max estimation (min-estimation head))]
            (if (empty? new-saw)
              (recur (disj available head) saw new-estimation wanted)
              (recur (apply conj (disj available head) (vals new-saw)) (merge saw new-saw) new-estimation wanted)))
          (let [score (end-score head)]
            (cond (empty? wanted) (recur (disj available head) saw (max estimation score) [head score])
              (> score (nth wanted 1)) (recur (disj available head) saw (max estimation score) [head score])
              :else (recur (disj available head) saw estimation wanted))))
        wanted))))

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y] ;x, y <= 10
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))