(ns ^:figwheel-always figwheel-dots.core
  (:require
    [cljs.core.async :refer [timeout chan >! <!]])
  (:require-macros
    [cljs.core.async.macros :refer [go go-loop]]))

(enable-console-print!)

(println "Edits to this text should show up in your developer console.")

;; define your app data so that it doesn't get over-written on reload

(defonce app-state (atom [{:x 50 :y 50 :color "lightgreen" :radius 30 :growing false}
                          {:x 200 :y 200 :color "blue" :radius 60 :growing false}
                          {:x 450 :y 450 :color "lightgreen" :radius 20 :growing true}]))
(defonce running (atom true))

(def canvas (-> js/document (.getElementById "canvas")))
(def context (.getContext canvas "2d"))
(def width (.-width canvas))
(def height (.-height canvas))
(def background "white")
(def colors ["red" "pink" "lightblue" "green" "lightgreen" "orange" "yellow"])

(defn setText [context color style]
  (set! (.-fillStyle context) color)
  (set! (.-font context) style))

(defn setColor [context color]
  (set! (.-fillStyle context) color)
  (set! (.-globalAlpha context) 1.0))

(defn draw-dot [{:keys [x y color radius]}]
  (doto context
    (setColor color)
    .beginPath
    (.arc x y radius 0 (* 2 Math/PI) true)
    .closePath
    .fill))

(defn draw-dots [state]
  (doall (map draw-dot @state)))

(defn jiggle [current]
  (+ current (rand-nth (range -1 1))))

(defn normalize [lower-bound upper-bound value]
  (cond
    (< value lower-bound)
    lower-bound
    (> value upper-bound)
    upper-bound
    :default
    value))

(def min-radius 20)
(def max-radius 80)

(defn update-radius [{:keys [radius growing] :as dot}]
  (cond
    (= radius max-radius)
    (assoc dot :growing false :radius (dec radius))
    (= radius min-radius)
    (assoc dot :growing true :radius (inc radius))
    growing
    (assoc dot :radius (inc radius))
    :default
    (assoc dot :radius (dec radius))))

(defn update-coors [{:keys [x y] :as dot}]
  (let [step 1
        direction (rand-nth [:northwest :northeast :southwest :southeast])]
    (case direction
      :northwest
      (assoc dot :x (- x step) :y (- y step))
      :northeast
      (assoc dot :x (+ x step) :y (- y step))
      :southwest
      (assoc dot :x (- x step) :y (+ y step))
      :southeast
      (assoc dot :x (+ x step) :y (+ y step)))))

(defn dot-work [{:keys [id x y val] :as dot}]
  (let [refresh-rate 4
        new-dot dot
        ;new-dot (if (= 1 (rand-int refresh-rate))
        ;          (assoc new-dot :color (rand-nth colors))
        ;          new-dot)
        new-dot (update-radius new-dot)
        new-radius (:radius new-dot)
        new-dot (-> new-dot
                    update-coors
                    (update :x #(normalize new-radius (- width new-radius) %))
                    (update :y #(normalize new-radius (- height new-radius) %)))
        ]
    new-dot))

(defn touching? [x1 x2 y1 y2 r1 r2]
  (let [distance (Math/sqrt (+ (Math/pow (- x2 x1) 2) (Math/pow (- y2 y1) 2)))]
    (< distance (+ r1 r2))))

(defn- all-different?
  "Annoyingly, the built-in distinct? doesn't handle 0 args, so we need
to write our own version that considers the empty-list to be distinct"
  [s]
  (if (seq s)
    (apply distinct? s)
    true))

;; so this code works with both 1.2.x and 1.3.0:
(def ^{:private true} plus +)
(def ^{:private true} mult *)

(defn- index-combinations
  [n cnt]
  (lazy-seq
    (let [c (vec (cons nil (for [j (range 1 (inc n))] (+ j cnt (- (inc n)))))),
          iter-comb
          (fn iter-comb [c j]
            (if (> j n) nil
              (let [c (assoc c j (dec (c j)))]
                (if (< (c j) j) [c (inc j)]
                  (loop [c c, j j]
                    (if (= j 1) [c j]
                      (recur (assoc c (dec j) (dec (c j))) (dec j)))))))),
          step
          (fn step [c j]
            (cons (rseq (subvec c 1 (inc n)))
                  (lazy-seq (let [next-step (iter-comb c j)]
                              (when next-step (step (next-step 0) (next-step 1)))))))]
      (step c 1))))

;; Helper function for bounded-distributions
(defn- distribute [m index total distribution already-distributed]
  (loop [distribution distribution
         index index
         already-distributed already-distributed]
    (if (>= index (count m)) nil
      (let [quantity-to-distribute (- total already-distributed)
            mi (m index)]
        (if (<= quantity-to-distribute mi)
          (conj distribution [index quantity-to-distribute total])
          (recur (conj distribution [index mi (+ already-distributed mi)])
                 (inc index)
                 (+ already-distributed mi)))))))

;; Helper function for bounded-distributions
(defn- next-distribution [m total distribution]
  (let [[index this-bucket this-and-to-the-left] (peek distribution)]
    (cond
      (< index (dec (count m)))
      (if (= this-bucket 1)
        (conj (pop distribution) [(inc index) 1 this-and-to-the-left])
        (conj (pop distribution)
              [index (dec this-bucket) (dec this-and-to-the-left)]
              [(inc index) 1 this-and-to-the-left])),
      ; so we have stuff in the last bucket
      (= this-bucket total) nil
      :else
      (loop [distribution (pop distribution)],
        (let
          [[index this-bucket this-and-to-the-left] (peek distribution),
           distribution (if (= this-bucket 1)
                          (pop distribution)
                          (conj (pop distribution)
                                [index (dec this-bucket) (dec this-and-to-the-left)]))],
          (cond
            (<= (- total (dec this-and-to-the-left)) (apply + (subvec m (inc index))))
            (distribute m (inc index) total distribution (dec this-and-to-the-left)),

            (seq distribution) (recur distribution)
            :else nil))))))

;; Helper function for multi-comb
(defn- bounded-distributions
  [m t]
  (let [step
        (fn step [distribution]
          (cons distribution
                (lazy-seq (when-let [next-step (next-distribution m t distribution)]
                            (step next-step)))))]
    (step (distribute m 0 t [] 0))))

;; Combinations of multisets
;; The algorithm in Knuth generates in the wrong order, so this is a new algorithm
(defn- multi-comb
  "Handles the case when you want the combinations of a list with duplicate items."
  [l t]
  (let [f (frequencies l),
        v (vec (distinct l)),
        domain (range (count v))
        m (vec (for [i domain] (f (v i))))
        qs (bounded-distributions m t)]
    (for [q qs]
      (apply concat
             (for [[index this-bucket _] q]
               (repeat this-bucket (v index)))))))

(defn combinations
  "All the unique ways of taking t different elements from items"
  [items t]
  (let [v-items (vec (reverse items))]
    (if (zero? t) (list ())
      (let [cnt (count items)]
        (cond (> t cnt) nil
              (= t 1) (for [item (distinct items)] (list item))
              (all-different? items) (if (= t cnt)
                                        (list (seq items))
                                        (map #(map v-items %) (index-combinations t cnt))),
              :else (multi-comb items t))))))

(defn valid? [state]
  (every?
    (fn [[dot1 dot2]]
      (not (touching? (:x dot1) (:x dot2) (:y dot1) (:y dot2) (:radius dot1) (:radius dot2))))
    (combinations state 2)))

(defn work-dots [state]
  (loop []
    (let [new-state (map dot-work @state)]
      (if (valid? new-state)
        (reset! state new-state)
        (recur)))))

(defn clear []
  (doto context
    (setColor background)
    (.fillRect  0 0 width height)))

(defn tick []
  (work-dots app-state)
  (clear)
  (draw-dots app-state))

(defn time-loop []
  (go
    (<! (timeout 1))
    (tick)
    (.requestAnimationFrame js/window time-loop)))

(defn run []
  (.requestAnimationFrame
    js/window
    (fn [_]
      (time-loop))))

(run)

(defn on-js-reload []
  ;; optionally touch your app-state to force rerendering depending on
  ;; your application
  ;; (swap! app-state update-in [:__figwheel_counter] inc)
  )
