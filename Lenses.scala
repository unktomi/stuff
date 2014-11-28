package main.scala.test.lenses

/**
 * Created by christopheroliver on 10/18/14.
 */

import Lenses._
import Prisms._

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
}

// 1 / A
trait Setter[A] extends AbstractSetter[Unit, A, Unit] {
  // 1 / A * A = 1
  def set(x: A): Unit
  // 1 / A * 1 * A = 1
  override def set(x: Unit, y: A): Unit = set(y)
}
/*
trait AbstractObservable[A, B, Z] extends AbstractObserver[A, AbstractObserver[Z, B]] {
  // (A, (A, B)=>A) => A
  override def set(x: A, y: AbstractObserver[Z, B]): A

  def map[C](f: B=>C): AbstractObservable[A, C, Z] = {
    val self = this
    new AbstractObservable[A, C, Z] {
      override def set(x1: A, y1: AbstractObserver[Z, C]): A = {
         self.set(x1, new AbstractObserver[Z, B] {
           override def set(x2: Z, y2: B): Z = {
              y1.set(x2, f(y2))
           }
         })
      }
    }
  }

  def flatmap[C](f: B=>AbstractObservable[A, C, Z]): AbstractObservable[A, C, Z] = {
    val self = this
    new AbstractObservable[A, C, Z] {
      override def set(x1: A, y1: AbstractObserver[Z, C]): A = {
        self.set(x1, new AbstractObserver[Z, B] {
          override def set(x2: Z, y2: B): Z = {
            val inner = f(y2)
            inner.set(x1, new AbstractObserver[Z, C] {
              override def set(x3: Z, y3: C): Z = {
                 y1.set(x3, y3)
              }
            })
          }
        })
      }
    }
  }

  def fold[C](z: C, f: (C, B)=>C): AbstractObservable[A, C, Z] = {
    val self = this
    new AbstractObservable[A, C, Z] {
      override def set(x1: A, y1: AbstractObserver[Z, C]): A = {
        self.set(x1, new AbstractObserver[Z, B] {
          var acc: C = z
          override def set(x2: Z, y2: B): Z = {
            acc = f(acc, y2)
            y1.set(x2, acc)
          }
        })
      }
    }
  }
}
*/
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

// (A / B)
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

trait Golden[F[_], A] extends ISO[F[F[A]], F[A] + A] {
  def unit(x: A): F[A]
  def counit(xs: F[A]): A
  def join(xs:F[F[A]]): F[A]
  def cojoin(xs: F[A]): F[F[A]]
  override def fw(x: F[F[A]]): F[A] + A = {
     val y: F[A] = join(x)
     val z: A = counit(y)
     val q: F[A] = unit(z)
     if (q == y) Right(z) else Left(y)
  }

  override def bw(y: F[A] + A): F[F[A]] = {
    y match {
      case Left(x) => cojoin(x)
      case Right(y) => cojoin(unit(y))
    }
  }
}




object Lenses {

  type AbstractObserver[A, B] = AbstractSetter[A, B, A]

  type Id[A] = A
  type *[A, B] = (A, B)
  type /[A, B] = Lens[A, B]

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
  }

  // A AND B IMPLIES C = (A IMPLIES B) IMPLIES C
  def curry[A, B, C](f: (A, B)=>C): A=>(B=>C) = {
    (x: A) => {
      (y: B) => f(x, y)
    }
  }

  def uncurry[A, B, C](f: A=>(B=>C)): (A, B)=>C = {
    (x: A, y: B) => {
      f(x)(y)
    }
  }

}
