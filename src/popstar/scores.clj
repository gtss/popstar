(ns popstar.scores
  (:require [clojure.set]))

(defn mp ([x] (do (prn x) x))
  ([x pred] (do (when (pred x) (prn x)) x)))

(def score (vec (concat [0 0] (for [n (range 2 101)] (* 5 n n)))))

(def line-index (range 10))

(def bonus-vec (vec (for [n line-index] (- 2000 (* 20 n n)))))

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

(def line-length (range 11))

(def cached-index-lines
  (vec (for [x line-index]
         (vec (for [length line-length]
                (inner-vec x length))))))

(def get-line (comp (partial get-in cached-index-lines) vector))

(def map-count (partial map count))

(def index-matrix (comp vec (partial map-indexed get-line) map-count))

(def +seq (partial apply +))

(def count-matrix (comp +seq map-count))

(def complement-nil? (complement nil?))

(defn color-line [table line-state]
  (mapv (partial get-color table) line-state))

(def ^:dynamic dynamic-color-line color-line)

(defn when= [l r v] (when (= l r) v))

(defn same-indexs [line-state last-line-state]
  (set (filter complement-nil? (map when= line-state last-line-state line-index))))

(def ^:dynamic dynamic-same-indexs same-indexs)

(defn same-color-line [cline]
  (mapv = cline (cons nil cline)))

(def ^:dynamic dynamic-same-color-line same-color-line)

(defn xy-component-maker [x j]
  (let [head [x j] lastp [x (dec j)] p2 [(dec x) j]]
    (fn [[mpi mii]]
      (let [lasti (mpi lastp)
            p2i (mpi p2)
            lastii (get mii lasti lasti)
            p2ii (get mii p2i p2i)
            new-mii (cond (> lastii p2ii) (conj mii [lasti p2ii])
                      (< lastii p2ii) (conj mii [p2i lastii])
                      :else mii)]
        [(conj mpi [head lasti]) new-mii]))))

(def cached-xy-component (mapv (fn [x] (mapv #(xy-component-maker x %) line-index)) line-index))

(defn x-component-maker [x j]
  (let [head [x j] lastp [x (dec j)]]
    (fn [[mpi mii]]
      (let [lasti (mpi lastp)]
        [(conj mpi [head lasti]) mii]))))

(def cached-x-component (mapv (fn [x] (mapv #(x-component-maker x %) line-index)) line-index))

(defn y-component-maker [x j]
  (let [head [x j] p2 [(dec x) j]]
    (fn [[mpi mii]]
      (let [p2i (mpi p2)]
        [(conj mpi [head p2i]) mii]))))

(def cached-y-component (mapv (fn [x] (mapv #(y-component-maker x %) line-index)) line-index))

(defn i-component-maker [x j i]
  (let [hv [[x j] i]]
    (fn [[mpi mii]]
      [(conj mpi hv) mii])))

(def cached-i-component (mapv (fn [x] (mapv (fn [j] (mapv #(i-component-maker x j %) (range 99))) line-index)) line-index))

(defn reverse-call [o f]
  (f o))

(defn simple-reverse-comp [aseq]
  (fn [obj]
    (reduce reverse-call obj aseq)))

(defn one-line-group [line-state same-ys x]
  (let [base (* 10 x)]
    (simple-reverse-comp
      (reduce-kv
        (fn [fs j hs]
          (let [sc (contains? same-ys j)]
            (cond
              (and sc hs) (conj fs (get-in cached-xy-component [x j]))
              hs (conj fs (get-in cached-x-component [x j]))
              sc (conj fs (get-in cached-y-component [x j]))
              :else (conj fs (get-in cached-i-component [x j (+ base j)])))))
        [] line-state))))

(def ^:dynamic dynamic-one-line-group one-line-group)

(def base-line-group-pair [[{} {}] nil])

(defn line-group-reducer [table [inner-pair lastl] index line-state]
  (let [lc (dynamic-color-line table line-state)
        si (if lastl (dynamic-same-indexs lc lastl) #{})]
    [((dynamic-one-line-group (dynamic-same-color-line lc) si index) inner-pair) lc]))

(defn line-group
  ([table]
    (let [state (index-matrix table)]
      (line-group table state)))
  ([table state]
    (first (reduce-kv (partial line-group-reducer table)
             base-line-group-pair state))))

(def count-pred (comp (partial < 1) count))

(defn group-from-line-group [[mpi mii]]
  (filter count-pred (vals (group-by #(let [i (mpi %)] (get mii i i)) (keys mpi)))))

(def group (comp group-from-line-group line-group))

(def partial-filterv-complement-nil? (partial filterv complement-nil?))

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

(def v0 [0])

(def v1 [1])

(defn merge-info-to-vector-from-a-seq [vector-c2 aseq]
  (let [n (count aseq)]
    (if (== 1 n)
      (update-in vector-c2 v1 inc)
      (update-in vector-c2 v0 (partial + (score n))))))

(def v00 [0 0])

(defn simple-max-estimation [path]
  (let [gs (vals (apply merge-with concat
                   (map (partial group-by (partial get-color (:table path))) (current-state path))))
        tmp (reduce merge-info-to-vector-from-a-seq v00 gs)]
    (+ (total-score path) (first tmp) (bonus (second tmp)))))

(def comp-score-count (comp score count))

(defn simple-min-estimation [path]
  (let [gs (groups path)
        all-n (count-matrix (current-state path))]
    (+seq (total-score path) (bonus (- all-n (count-matrix gs))) (map comp-score-count gs))))

(defn path-groups [path]
  (group (:table path) (current-state path)))

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
  (let [actions-fn (memoize (fn [_] (conj (actions prev-path) last-action)))
        path-total-score-fn (memoize (fn [_] (+ (total-score prev-path) (comp-score-count last-action))))
        current-state-fn (memoize (fn [_] (eliminate (current-state prev-path) last-action)))]
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
  (condp == (compare (total-score path1) (total-score path2))
    1 :gt ;
    -1 :lt ;
    0 :eq ;
    :nc ))

(def fset #{nil :nc })

(def gset #{:gt :nc })

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
                  (if (contains? fset result)
                    (recur tail)
                    result))
                default-value)))))

(def path-comparator #(if (= %1 %2)
                        0
                        (let [me1 (min-estimation %1)
                              me2 (min-estimation %2)]
                          (cond
                            (< me1 me2) 1
                            (> me1 me2) -1
                            :else (let [ts1 (total-score %1)
                                        ts2 (total-score %2)]
                                    (cond
                                      (< ts1 ts2) 1
                                      (> ts1 ts2) -1
                                      :else (let [cg1 (count (groups %1))
                                                  cg2 (count (groups %2))]
                                              (if (> cg1 cg2) 1
                                                -1))))))))

(defn children-reducer [[result-set result-map result-long :as prev] path]
  (let [state (current-state path)
        difference (cond
                     (contains? result-map state) (diff path (result-map state))
                     (> result-long (max-estimation path)) :lt ;
                     :else :nc )]
    (if (contains? gset difference)
      [(conj result-set path) (conj result-map [state path]) (max result-long (min-estimation path))]
      prev)))

(defn popstars [table]
  (binding [dynamic-same-indexs (memoize same-indexs)
            dynamic-one-line-group (memoize (comp memoize one-line-group))
            dynamic-same-color-line (memoize same-color-line)
            dynamic-color-line (memoize color-line)]
    (loop [available (sorted-set-by path-comparator (first-lazy-cached-path table))
           saw {} estimation 0 wanted nil]
      (if-let [head (first available)]
        (let [others (disj available head)]
          (if-let [head-groups (not-empty (groups head))]
            (let [paths (map #(next-lazy-cached-path head %) head-groups)
                  [new-available new-saw new-estimation] (reduce children-reducer [others saw estimation] paths)]
              (recur new-available new-saw (long new-estimation) wanted))
            (let [score (end-score head)]
              (if (or (nil? wanted) (> score (nth wanted 1)))
                (recur others saw (max estimation score) [head score])
                (recur others saw estimation wanted)))))
        wanted))))

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y] ;x, y <= 10
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))