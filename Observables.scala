package main.scala.test.lenses

import scala.collection.mutable
import Observables._
import Lenses._

// type SetterOfSetter[A] = Setter[Setter[A]]
trait SetterOfSetter[A] {

  override def finalize(): Unit = {
    println("Finalize: "+this)
  }

  def setSetter(xs: Setter[A]): Unit

  // Scala for-comprehension hooks

  // functor
  def map[B](f: A=>B): SetterOfSetter[B] = {
    val xs = this
    new SetterOfSetter[B] {
      def setSetter(ys: Setter[B]): Unit = {
        xs.setSetter(new Setter[A] {
          def set(x: A): Unit = {
            ys.set(f(x))
          }
        })
      }
    }
  }

  // monad
  def flatMap[B](f: A=>SetterOfSetter[B]): SetterOfSetter[B] = {
    val outer: SetterOfSetter[A] = this
    new SetterOfSetter[B] {
      def setSetter(xs: Setter[B]): Unit = {
        outer.setSetter(new Setter[A] {
          def set(x: A): Unit = {
            val inner: SetterOfSetter[B] = f(x)
            inner.setSetter(xs)
          }
        })
      }
    }
  }

  var ob: Observed[A] = null

  def toObserved(): Observed[A] = {
    if (ob == null) {
      val self = this
      val x = new MutableCellImpl[A](None) {
        override def toObservable(): SetterOfSetter[A] = self
      }
      setSetter(x)
      ob = x
    }
    ob
  }

  def fold[B](z: B, f: (B, A)=>B): Observable[B] = {
    val self = this
    new Observable[B] {
      def setSetter(xs: Setter[B]): Unit = {
        self.setSetter(new Setter[A] {
          var acc: B = z
          def set(x: A): Unit = {
            acc = f(acc, x)
            xs.set(acc)
          }
        })
      }
    }
  }

  def take(n: Int): SetterOfSetter[A] = takeAndThen(n, nop)
  def drop(n: Int): SetterOfSetter[A] = nop.takeAndThen(n, this)

  def takeAndThen(n: Int, andThen: SetterOfSetter[A]): SetterOfSetter[A] = {
    val self = this
    new SetterOfSetter[A] {
      override def setSetter(xs: Setter[A]): Unit = {
        self.setSetter(new Setter[A] {
          var taken = 0
          override def set(x: A): Unit = {
            taken = taken + 1
            if (taken <= n) {
              xs.set(x)
            } else if (taken == n+1) {
              andThen.setSetter(xs)
              gc(this)
            }
          }
        })
      }
    }
  }

  def or (other: SetterOfSetter[A]): SetterOfSetter[A] = merge(other)

  def merge(other: SetterOfSetter[A]): SetterOfSetter[A] = {
    val self = this
    new SetterOfSetter[A] {
      def setSetter(xs: Setter[A]): Unit = {
        self.setSetter(xs)
        other.setSetter(xs)
      }
    }
  }

  def takeUntil[B](signal: SetterOfSetter[B], andThen: SetterOfSetter[A] = nop): SetterOfSetter[A] = {
    val self = this
    new SetterOfSetter[A] {
      def setSetter(xs: Setter[A]): Unit = {
        var done = false
        var switched = false
        val test = new Setter[B] {
          def set(x: B): Unit = done = true
        }
        signal.setSetter(test)
        self.setSetter(new Setter[A] {
          var taken = 0
          override def set(x: A): Unit = {
            if (!done) {
              xs.set(x)
            } else if (!switched) {
              switched = true
              andThen.setSetter(xs)
              gc(this)
            }
          }
        })
      }
    }
  }

  def followedBy(xs: SetterOfSetter[A]): SetterOfSetter[A] = {
    takeAndThen(1, xs)
  }

  def filter(p: A=>Boolean): Observable[A] = {
    val self = this
    new Observable[A] {
      override def setSetter(xs: Setter[A]): Unit = {
        self.setSetter(new Setter[A] {
          override def set(x: A): Unit = {
            if (p(x)) xs.set(x)
          }
        })
      }
    }
  }

  def repeat(n: Int): Observable[A] = {
    val self = this
    new Observable[A] {
      override def setSetter(xs: Setter[A]): Unit = {
        self.setSetter(new Setter[A] {
          override def set(x: A): Unit = {
            for { i <- 0 until n } xs.set(x)
          }
        })
      }
    }
  }
}


/**
 * Created by christopheroliver on 10/29/14.
 */

object Observables {

  val roots = new mutable.WeakHashMap[Setter[_], mutable.Set[SetterOfSetter[_]]]

  def gc[A](xs: Setter[A]): Unit = {
    //println("gc: "+xs)
    roots.get(xs) match {
      case None =>
      case Some(ys) => {
        roots.remove(xs)
      }
    }
  }

  def nop[A] = new SetterOfSetter[A] {
    def setSetter(xs: Setter[A]): Unit = {}
  }
  type Observer[A] = Setter[A]
  type Observed[A] = Getter[A]
  type Observable[A] = SetterOfSetter[A]
  trait Subject[A] extends Observable[A] with Observer[A]
  trait MutableCell[A] extends Observed[A] with Observer[A] with (Unit / A) {
    override def get(nothing: Unit): A = get()
    override def set(nothing: Unit, x: A): Unit = set(x)
  }

  // (A=>())=>() AND A=>()
  class SubjectImpl[A] extends Subject[A] {
    private val subscribers = new mutable.WeakHashMap[Setter[A], Unit]
    def setSetter(x: Setter[A]): Unit = {
      subscribers.put(x, ())
      val xs = roots.get(x)
      xs match {
        case None => {
          val s = new mutable.HashSet[SetterOfSetter[_]]
          roots.put(x, s)
          s.add(this)
        }
        case Some(y) => y.add(this)
      }
    }
    def set(x: A): Unit = {
      val todo = for { y <- subscribers.keySet } yield (()=> y.set(x))
      for (f <- todo) f()
    }
    def toObservable(): SetterOfSetter[A] = this
  }

  class MutableCellImpl[A](init: Option[A]) extends MutableCell[A] {
    var value: Option[A] = init
    override def set(x: A): Unit = {
      val newValue = Some(x)
      if (value != newValue) {
        value = newValue
        notifyObservers()
      }
    }
    override def get(): A = value.get

    var subj: Subject[A] = null
    def toObservable(): SetterOfSetter[A] = {
      val self = this
      if (subj == null) {
        subj = new SubjectImpl[A] {
          override def toObserved(): Observed[A] = self
        }
      }
      subj
    }

    def notifyObservers(): Unit = {
      if (subj != null) subj.set(get())
    }
  }

  def ref[A] = new MutableCellImpl[A](None)
  def ref[A](x: A) = new MutableCellImpl[A](Some(x))
  def subject[A] = new SubjectImpl[A]


  def Println[A](prefix: String): Setter[A] = new Setter[A] {
    override def set(x: A): Unit = {
      println(prefix + x)
    }
  }

  def observe[A](x: A): SetterOfSetter[A] = new SetterOfSetter[A] {
    def setSetter(xs: Setter[A]): Unit = {
      xs.set(x)
    }
  }

  def main(argv: Array[String]): Unit = {
    def mouseSim: Unit = {
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
      mouseArmed.setSetter(arm)
      mouseDisarmed.setSetter(disarm)
      mouseTrigger.setSetter(trig)

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
      val g = clickCount.toObserved()
      val onClick = Println[Unit]("clicked=")
      clicks.setSetter(onClick)
      clicks.set(())
      println(g.get())
      clicks.set(())
      println(g.get())
      arm = null
      disarm = null
      trig = null
      for { i <- 0 to 10 } System.gc()
    }

    mouseSim
  }

}
