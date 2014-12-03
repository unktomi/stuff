package main.scala.test.lenses

/**
 * Created by christopheroliver on 10/18/14.
 */

import Lenses._


import scala.collection.mutable


//import Prisms._

trait Functor[F[_]] {
  def map[A, B](xs: F[A], f: A=>B): F[B]
}

trait AbstractGetter[S, A] {

  def get(x: S): A

  def toPrism: Prism[A, S] = {
    new Prism[A, S] {
      override def raise(x: S): A = get(x)
      override def handle(y: A): S + A = Right(y)
    }
  }

  def toState: S=>(S, A) = {
    (x: S) => {
      (x, get(x))
    }
  }
}

trait AbstractSetter[S, B, T] {
  def set(x: S, y: B): T
}

// A / 1
trait Getter[A] extends AbstractGetter[Unit, A] {
  // A / 1 * 1 = A

  override def get(nothing: Unit): A = get()
  def get(): A
  def map[B](f: A=>B): Getter[B] = {
      val self = this
      new Getter[B] {
        override def get(): B = {
           f(self.get())
        }
      }
  }
  /*
  def flatMap[B](f: A=>Getter[B]): Getter[B] = {
    val self = this
    new Getter[B] {
      override def get(): B = {
        f(self.get()).get()
      }
    }
  }
  */

}

// 1 / A
trait Setter[A] extends AbstractSetter[Unit, A, Unit] {
  // 1 / A * A = 1
  def set(x: A): Unit
  // 1 / A * 1 * A = 1
  override def set(x: Unit, y: A): Unit = set(y)
}

trait AbstractLens[S, T, A, B] extends AbstractGetter[S, A] with AbstractSetter[S, B, T] {
  def apply[F[_]](unit: A => F[B])(implicit fun: Functor[F]): S => F[T] = {
    (pos: S) => fun.map(unit(get(pos)), (x: B) => set(pos, x))
  }
  // project A from x
  def get(x: S): A
  // replace B in x with y
  def set(x: S, y: B): T

  def toCoState(x: S): (A, B=>T) = {
    (get(x), (y: B)=>(set(x, y)))
  }
}

trait MutableCell[A] extends (Unit / A) with Getter[A] with Setter[A]

// A = (B, R)
// R = A / B

trait Lens[A, B] extends AbstractLens[A, A, B, B] {
  type This = A / B

  // project B from x
  // This * A = B
  // A / B * A = B
  def get(x: A): B
  // replace B in x with y
  // This / A  * B = A
  // (A / B) / A * B = A
  def set(x: A, y: B): A

  def swap() = invert()

  def invert(): (B / A) = {
    val self = this
    new (B / A) {
      var store: Option[A] = None
      // "project" A from B - returns the result of setting x on the stored A
      def get(x: B): A = {
        self.set(store.get, x)
      }
      // "replace" A "in" B - since A actually contains B, the effect is to store the result of setting x in y
      def set(x: B, y: A): B = {
        store = Some(self.set(y, x))
        self.get(store.get)
      }
    }
  }

  // (A / B) * ( B / C ) =  A / C

  def *[C](y: B / C) = compose(y)

  // (A / B) . ( B / C ) =  A / C
  def compose[C](y: B / C): A / C= {
    val self = this
    new (A / C) {
      def get(x: A): C = y.get(self.get(x))
      def set(x: A, z: C): A = {
        self.set(x, y.set(self.get(x), z))
      }
    }
  }

  override def toState: (A) => (A, B) = super.toState

  override def toCoState(x: A): (B, (B) => A) = super.toCoState(x)
}

// A / A
case class One[A]() extends (A / A) {
  def get(x: A): A = x
  override def set(x: A, y: A): A = y
  override def invert: (A / A) = this
}

// Evidence A is isomorphic to (B * R)
// B / A = 1 / R
trait ISOLens[A, B, R] extends ISO[A, (B, R)] with (A / B) {
  def get(x: A): B = this.fw(x)._1
  def set(x: A, y: B): A = {
    val z = this.fw(x)
    this.bw((y, z._2))
  }

}

case class LeftLens[A, B]() extends (A / (A + B))  {
  // project B from x
  override def get(x: A): +[A, B] = Left(x)

  // replace B in x with y
  override def set(x: A, y: +[A, B]): A = y match {
    case Left(a) => a
    case Right(b) => x
  }
}

object Lenses {

  type Id[A] = A
  type *[A, B] = (A, B)
  type /[A, B] = Lens[A, B]
  type +[A, B] = Either[A, B]

  // A / A = 1
  def one[A]: (A / A) = One[A]

  // A / 1
  def just[A] = new (A / Unit) {
    // project Unit from A
    override def get(x: A): Unit = ()
    // replace nothing in x with nothing
    override def set(x: A, nothing: Unit): A = x
  }

  // (A * B) / A = B
  def former[A, B]: (A, B) / A  = new ((A, B) / A) {
    def get(xs: (A, B)): A = xs._1
    def set(xs: (A, B), y: A): (A, B) = (y, xs._2)
  }

  // (A * B) / B  = A
  def latter[A, B]: (A, B) / B  = new ((A, B) / B) {
    def get(xs: (A, B)): B = xs._2
    def set(xs: (A, B), y: B): (A, B) = (xs._1, y)
  }


  def laws[A, B](x: (A / B), y: A, z: B): Boolean = {
     x.get(x.set(y, z)) == z &&
      x.set(y, x.get(y)) == y &&
         x.set(x.set(y, z), z) == x.set(y, z)
  }

  def index[A](i: Int): Lens[Seq[A], A] = new Lens[Seq[A], A] {
    override def get(x: Seq[A]): A = x(i)
    override def set(x: Seq[A], y: A): Seq[A] = x.updated(i, y)
  }

  def arrayIndex[A](i: Int): Lens[Array[A], A] = new Lens[Array[A], A] {
    override def get(x: Array[A]): A = x(i)
    override def set(x: Array[A], y: A): Array[A] = { x.update(i, y); x }
  }


  def subject[A]: Subject[A] = new Subject[A] {}

  def observe[A](x: A): Observable[A] = new Observable[A] {
    override def set(nothing: Unit, y: Observer[A]): Unit = {
      y.raise(x)
    }
  }

  import Prisms._

  type Observer[A] = Unit - A

  trait Observable[A] extends AbstractSetter[Unit, Observer[A], Unit] {

    def subscribe(x: Observer[A]): Unit = set((), x)

    def map[B](f: A=>B): Observable[B] = {
      val self = this
      new Observable[B] {
        // 1 / A * A = 1
        override def set(nothing: Unit, ob: Observer[B]): Unit = {
          self.subscribe(new Observer[A] {
            // throw = dual of Lens.get
            override def raise(x: A): Unit = {
              ob.raise(f(x))
            }

            // inject A into E
            override def handle(y: Unit): Prisms.+[A, Unit] = {
              Right(())
            }
          })
        }
      }
    }

    def flatMap[B](f: A=>Observable[B]): Observable[B] = {
      val self = this
      new Observable[B] {
        // 1 / A * A = 1
        override def set(nothing: Unit, ob: Observer[B]): Unit = {
          self.subscribe(new Observer[A] {
            // throw = dual of Lens.get
            override def raise(x: A): Unit = {
              val inner = f(x)
              inner.set((), ob)
            }

            // inject A into E
            override def handle(y: Unit): Prisms.+[A, Unit] = {
              Right(())
            }
          })
        }
      }
    }

    def fold[B](z: B, f: (B, A)=>B): Observable[B] = {
      val self = this
      new Observable[B] {
        // 1 / A * A = 1
        override def set(nothing: Unit, xs: Observer[B]): Unit = {
          self.subscribe(new Observer[A] {
            var acc: B = z
            // throw = dual of Lens.get
            override def raise(x: A): Unit = {
              acc = f(acc, x)
              xs.raise(acc)
            }
            // inject A into E
            override def handle(y: Unit): A + Unit = {
              Right(())
            }
          })
        }
      }
    }

    def take(n: Int): Observable[A] = takeAndThen(n, nop)
    def drop(n: Int): Observable[A] = nop.takeAndThen(n, this)

    def takeAndThen(n: Int, andThen: Observable[A]): Observable[A] = {
      val self = this
      new Observable[A] {
        override def set(nothing: Unit, xs: Observer[A]): Unit = {
          self.subscribe(new Observer[A] {
            var taken = 0
            override def raise(x: A): Unit = {
              taken = taken + 1
              if (taken <= n) {
                xs.raise(x)
              } else if (taken == n+1) {
                andThen.set((), xs)
                gc(this)
              }
            }

            // inject A into E
            override def handle(y: Unit): A + Unit = Right(())
          })
        }
      }
    }

    def or (other: Observable[A]): Observable[A] = merge(other)

    def merge(other: Observable[A]): Observable[A] = {
      val self = this
      new Observable[A] {
        def set(nothing: Unit, xs: Observer[A]): Unit = {
          self.set((), xs)
          other.set((), xs)
        }
      }
    }

    def takeUntil[B](signal: Observable[B], andThen: Observable[A] = nop): Observable[A] = {
      val self = this
      new Observable[A] {
        def set(nothing: Unit, xs: Observer[A]): Unit = {
          var done = false
          var switched = false
          val test = new Observer[B] {
            def raise(x: B): Unit = done = true
            // inject A into E
            override def handle(y: Unit): B + Unit = Right(())
          }
          signal.set((), test)
          self.set((), new Observer[A] {
            var taken = 0
            override def raise(x: A): Unit = {
              if (!done) {
                xs.raise(x)
              } else if (!switched) {
                switched = true
                andThen.set((), xs)
                gc(this)
              }
            }
            override def handle(y: Unit): A + Unit = Right(())
          })
        }
      }
    }

    def followedBy(xs: Observable[A]): Observable[A] = {
      takeAndThen(1, xs)
    }

    def filter(p: A=>Boolean): Observable[A] = {
      val self = this
      new Observable[A] {
        override def set(nothing: Unit, xs: Observer[A]): Unit = {
          self.set(nothing: Unit, new Observer[A] {
            override def raise(x: A): Unit = {
              if (p(x)) xs.raise(x)
            }

            // inject A into E
            override def handle(y: Unit): A + Unit = {
               Right(())
            }
          })
        }
      }
    }

    def repeat(n: Int): Observable[A] = {
      val self = this
      new Observable[A] {
        override def set(nothing: Unit, xs: Observer[A]): Unit = {
          self.set((), new Observer[A] {
            override def raise(x: A): Unit = {
              for { i <- 0 until n } xs.raise(x)
            }
            // inject A into E
            override def handle(y: Unit): A + Unit = {
              Right(())
            }
          })
        }
      }
    }
  }

  case class Subject[A]() extends Observable[A] with (Unit / (Unit - A)) {

    val subscribers = new mutable.WeakHashMap[(Unit - A), Unit]

    var last: Option[A] = None

    override def get(x: Unit): Unit - A = {
       new (Unit - A) {
         // throw = dual of Lens.get
         override def raise(x: A): Unit = {
           last = Some(x)
           for (j <- subscribers.keySet) j.raise(x)
         }

         // inject A into E
         override def handle(y: Unit): A + Unit = {
             last match {
               case Some(x) => Left(x)
               case None => Right(())
             }
         }
       }
    }

    override def set(x: Unit, y: Unit - A): Unit = {
      subscribers.put(y, ())
      val xs = roots.get(y)
      xs match {
        case None => {
          val s = new mutable.HashSet[Observable[_]]
          roots.put(y, s)
          s.add(this)
        }
        case Some(y) => y.add(this)
      }
    }

    def set(x: A): Unit = {
      get(()).raise(x)
    }
  }

  val roots = new mutable.WeakHashMap[Unit - _, mutable.Set[Observable[_]]]

  def gc[A](xs: Unit - A): Unit = {
    //println("gc: "+xs)
    roots.get(xs) match {
      case None =>
      case Some(ys) => {
        roots.remove(xs)
      }
    }
  }

  def nop[A] = new Observable[A] {
    // 1 / A * A = 1
    override def set(nothing: Unit, x: Observer[A]): Unit = {}
  }


  def main(argv: Array[String]): Unit = {
    type Point = (Int, Int)  // Int * Int
    type Interval = (Point, Point)  // Point * Point

    val i = new Interval(new Point(3, 1), new Point(44, 22))
    val end: Interval / Point = latter
    val x: Point / Int = former
    val z: Interval / Int = end * x

    println("LENS LAWS "+laws(z, i, 100))

    println(z.get(i))

    val a = Array(i)
    var idx = arrayIndex[Interval](0)
    val z1 = idx * end * x
    println("LENS LAWS a " + laws(z1, a, 20))
    println(z1.get(a))
    def Println[A](prefix: String): Observer[A] = new Observer[A] {
      override def raise(x: A): Unit = {
        println(prefix + x)
      }

      // inject A into E
      override def handle(y: Unit): Prisms.+[A, Unit] = Right(())
    }
    def mouseSim {
      case class MouseEvent(val x: Int, val y: Int, val button: Int) {}

      val mouseDown = subject[MouseEvent]
      val mouseUp = subject[MouseEvent]
      val mouseMove = subject[MouseEvent]
      val mouseLeave = subject[MouseEvent]
      val mouseEnter = subject[MouseEvent]

      val mouseDrag = (mouseDown followedBy mouseMove) takeUntil mouseUp

      val mouseArmed = for {
        press <- mouseDown
        pressOrReenteredBeforeRelease <- observe(press) or (mouseEnter takeUntil mouseUp)
      } yield pressOrReenteredBeforeRelease

      val mouseDisarmed = for {
        arm <- mouseArmed
        nextLeaveOrRelease <- (mouseLeave or mouseUp) take 1
      } yield nextLeaveOrRelease

      val mouseTrigger = for {
        arm <- mouseArmed
        releaseBeforeLeave <- mouseUp takeUntil mouseLeave
      } yield releaseBeforeLeave

      var arm = Println[MouseEvent]("arm=")
      var disarm = Println[MouseEvent]("disarm=")
      var trig = Println[MouseEvent]("trigger=")
      mouseArmed.subscribe(arm)
      mouseDisarmed.subscribe(disarm)
      mouseTrigger.subscribe(trig)

      mouseEnter.set(new MouseEvent(3, 29, 0))
      mouseDown.set(new MouseEvent(3, 30, 1))
      mouseLeave.set(new MouseEvent(3, 50, 1))
      mouseEnter.set(new MouseEvent(3, 33, 1))
      mouseUp.set(new MouseEvent(3, 33, 1))
      mouseDown.set(new MouseEvent(3, 44, 1))
      mouseLeave.set(new MouseEvent(3, 54, 1))
      mouseEnter.set(new MouseEvent(3, 34, 1))

      val clicks = subject[Unit]

      val clickCount = clicks.fold(0, (x:Int, y: Unit)=> x + 1)

      val onClick = Println[Unit]("clicked=")
      clicks.subscribe(onClick)
      clicks.set(())

      clicks.set(())

      arm = null
      disarm = null
      trig = null
      for { i <- 0 to 10 } System.gc()
    }

    mouseSim
  }


}
