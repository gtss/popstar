(ns popstar.scores
  (:require [clojure.set]))

(defn mp ([x] (do (prn x) x))
  ([x pred] (do (when (pred x) (prn x)) x)))

(def score (doall (vec (concat [0 0] (for [n (range 2 101)] (* 5 n n))))))

(def line-index (doall (range 10)))

(def bonus-vec (doall (vec (for [n line-index] (- 2000 (* 20 n n))))))

(defn bonus [n] (if (>= n 10) 0 (nth bonus-vec n)))

(def colors #{:b :g :p :r :y})

(defn nth2 [matrix x y] (nth (nth matrix x) y))

(defn nth3 [matrix x y z] (nth (nth (nth matrix x) y) z))

;table [[:b :r :g ] [:p :r :r ] [:y :b :b ]]

;state [[[0 0] [0 2]] [[1 1] [1 2]] [[2 0] [2 1]]]

;point [0 1]

;color :g

(defn count-matrix [coll] (->> coll (map count) (reduce unchecked-add 0)))

(defn component-cache-maker [component-maker]
  (mapv (fn [x] (mapv #(component-maker x %) line-index)) line-index))

(defn xy-component-maker [x j]
  (let [head [x j] lastp [x (unchecked-dec j)] p2 [(unchecked-dec x) j]]
    (fn [[mpi mii]]
      (let [lasti (mpi lastp)
            p2i (mpi p2)
            lastii (get mii lasti lasti)
            p2ii (get mii p2i p2i)
            new-mii (cond (> lastii p2ii) (assoc mii lasti p2ii)
                          (< lastii p2ii) (assoc mii p2i lastii)
                          :else mii)]
        [(assoc mpi head lasti) new-mii]))))

(def cached-xy-component (component-cache-maker xy-component-maker))

(defn xy-component-selector [x j _]
  (nth2 cached-xy-component x j))

(defn x-component-maker [x j]
  (let [head [x j] lastp [x (unchecked-dec j)]]
    (fn [[mpi mii]]
      (let [lasti (mpi lastp)]
        [(assoc mpi head lasti) mii]))))

(def cached-x-component (component-cache-maker x-component-maker))

(defn x-component-selector [x j _]
  (nth2 cached-x-component x j))

(defn y-component-maker [x j]
  (let [head [x j] p2 [(unchecked-dec x) j]]
    (fn [[mpi mii]]
      (let [p2i (mpi p2)]
        [(assoc mpi head p2i) mii]))))

(def cached-y-component (component-cache-maker y-component-maker))

(defn y-component-selector [x j _]
  (nth2 cached-y-component x j))

(defn i-component-maker [x j i]
  (let [head [x j]]
    (fn [[mpi mii]]
      [(assoc mpi head i) mii])))

(def cached-i-component (mapv (fn [x] (mapv (fn [y] (mapv #(i-component-maker x y %) (range 100))) line-index)) line-index))

(defn i-component-selector [x j base]
  (nth3 cached-i-component x j (unchecked-add base j)))

(def nil10 (doall (vec (repeat 10 nil))))

(defn type-selector [current-color prev-color prev-line-color]
  (let [scx (identical? current-color prev-color)
        scy (identical? current-color prev-line-color)]
    (cond
      (and scy scx) xy-component-selector
      scx x-component-selector
      scy y-component-selector
      :else i-component-selector)))

(defn reverse-call [o f]
  (f o))

(def type-selector-maker #(fn [prev-line-color] (type-selector %1 %2 prev-line-color)))

(defn type-selectors-maker [cline]
  (let [ptss (mapv type-selector-maker cline (cons nil cline))]
    (fn [lcline]
      (mapv reverse-call (concat lcline nil10) ptss))))

(defn simple-reverse-comp [aseq]
  (fn [obj]
    (reduce reverse-call obj aseq)))

(defn one-line-group [type-selectors x]
  (let [base (unchecked-multiply 10 x)]
    (simple-reverse-comp
      (map-indexed
        (fn [j ts]
          (ts x j base)) type-selectors))))

(def base-line-group-pair [[{} {}] nil])

(defn line-group-reducer-maker [type-selectors-maker-fn one-line-group-fn]
  (fn [[inner-pair lastl] index line-color]
    (let [sml (type-selectors-maker-fn line-color)]
      [((one-line-group-fn (sml lastl) index) inner-pair) line-color])))

(def default-line-group-reducer (line-group-reducer-maker type-selectors-maker one-line-group))

(defn line-group [line-group-reducer state]
  (nth (reduce-kv line-group-reducer base-line-group-pair state) 0))

(defn select-group-by [f f2 coll]
  (persistent!
    (reduce
      (fn [ret x]
        (let [k (f x)]
          (assoc! ret k (conj (get ret k []) (f2 x)))))
      (transient {}) coll)))

(defn count-pred [coll] (->> coll count (< 1)))

(defn group-by-pred-maker [mii]
  (fn [e]
    (let [i (val e)]
      (get mii i i))))

(defn group-from-line-group [[mpi mii]]
  (filter count-pred (vals (select-group-by (group-by-pred-maker mii) key mpi))))

(defn group [line-group-reducer state] (group-from-line-group (line-group line-group-reducer state)))

(def filterv-identity #(filterv identity %))

(defn assoc-matrix [matrix [x y] v]
  (assoc matrix x (assoc (nth matrix x) y v)))

(def assoc-matrix-nil #(assoc-matrix %1 %2 nil))

(defn eliminate [state agroup]
  (filterv not-empty
           (mapv filterv-identity
                 (reduce assoc-matrix-nil state agroup))))

(defprotocol Path
  (groups [path])
  (actions [path])
  (^long total-score [path])
  (current-state [path])
  (max-estimation [path])
  (^long min-estimation [path]))

(defrecord LazyCachedPath [table groups-fn actions-fn total-score-fn current-state-fn max-estimation-fn min-estimation-fn]
  Path
  (groups [path]
    (groups-fn path))
  (actions [path]
    (actions-fn path))
  (total-score [path]
    (total-score-fn path))
  (current-state [path]
    (current-state-fn path))
  (max-estimation [path]
    (max-estimation-fn path))
  (min-estimation [path]
    (min-estimation-fn path)))

(defn end-score
  (^long [path]
   (unchecked-add (total-score path) (-> path current-state count-matrix bonus))))

(def >1 #(> % 1))

(defn simple-max-estimation [^LazyCachedPath path]
  (let [fc (frequencies (apply concat (current-state path)))
        ss (filter >1 (vals fc))]
    (reduce unchecked-add (unchecked-add (total-score path) (bonus (unchecked-subtract (count fc) (count ss))))
            (map score ss))))

(defn comp-score-count [coll] (-> coll count score))

(defn simple-min-estimation [path]
  (let [gs (groups path)
        all-n (count-matrix (current-state path))]
    (reduce unchecked-add (unchecked-add (total-score path) (bonus (unchecked-subtract all-n (count-matrix gs))))
            (map comp-score-count gs))))

(defn path-groups [^LazyCachedPath path]
  (group default-line-group-reducer (current-state path)))

(defn empty-actions [_] [])

(defn zero-score [_] 0)

(defn memoize1 [f]
  (let [mem (atom nil)]
    (fn [arg]
      (if-let [e @mem]
        e
        (reset! mem (f arg))))))

(defn first-lazy-cached-path [table group-fn]
  (->LazyCachedPath
    table
    (memoize1 group-fn)
    empty-actions
    zero-score
    (fn [_] table)
    (memoize1 simple-max-estimation)
    (memoize1 simple-min-estimation)))

(defn next-lazy-cached-path [table group-fn ^LazyCachedPath prev-path last-action]
  (let [actions-fn (memoize1 (fn [_] (conj (actions prev-path) last-action)))
        path-total-score-fn (memoize1 (fn [_] (unchecked-add (total-score prev-path) (comp-score-count last-action))))
        current-state-fn (memoize1 (fn [_] (eliminate (current-state prev-path) last-action)))]
    (->LazyCachedPath
      table
      (memoize1 group-fn)
      actions-fn
      path-total-score-fn
      current-state-fn
      (memoize1 simple-max-estimation)
      (memoize1 simple-min-estimation))))

(def differences #{:lt :gt :eq :nc}) ;nc is not comparable

(defn score-differ [path1 path2]
  (condp == (compare (total-score path1) (total-score path2))
    1 :gt ;
    -1 :lt ;
    0 :eq ;
    :nc))

(def fset #{nil :nc})

(def gset #{:gt :nc})

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
                     :else :nc)]
    (if (contains? gset difference)
      [(conj result-set path) (assoc result-map state path) (max result-long (min-estimation path))]
      prev)))

(defn popstars [table]
  (let [one-line-group-fn (memoize #(memoize (one-line-group %1 %2)))
        selectors-maker-fn (memoize #(memoize (type-selectors-maker %)))
        line-group-reducer (line-group-reducer-maker selectors-maker-fn one-line-group-fn)
        group-fn (fn [path]
                   (group line-group-reducer (current-state path)))]
    (loop [available (sorted-set-by path-comparator (first-lazy-cached-path table group-fn))
           saw {} estimation 0 wanted-score 0 wanted nil]
      (if-let [head (first available)]
        (let [others (disj available head)]
          (if-let [head-groups (not-empty (groups head))]
            (let [paths (map #(next-lazy-cached-path table group-fn head %) head-groups)
                  [new-available new-saw new-estimation] (reduce children-reducer [others saw estimation] paths)]
              (recur new-available new-saw (long new-estimation) wanted-score wanted))
            (let [score (end-score head)]
              (if (or (nil? wanted) (> score wanted-score))
                (recur others saw estimation score head)
                (recur others saw estimation wanted-score wanted)))))
        [wanted-score wanted]))))

(defn rand-color []
  (rand-nth (vec colors)))

(defn rand-table [x y] ;x, y <= 10
  (vec (for [a (range x)] (vec (for [b (range y)] (rand-color))))))