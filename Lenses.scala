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

trait AbstractLens[S, T, A, B] extends AbstractGetter[S, A] with AbstractSetter[S, B, T] {
  def apply[F[_]](peek: A => F[B], pos: S)(implicit fun: Functor[F]): F[T] = {
    fun.map(peek(get(pos)), (x: B) => set(pos, x))
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

trait Monoid[A] {
  def z: A
  def reduce(x: A, y: A): A
}

case class AddInt() extends Monoid[Int] {
  def z = 0
  def reduce(x: Int, y: Int): Int = x + y
}

trait Comonoid[A] {
  def z: A
  def split(x: A): (A, A)
}

trait Golden[A] extends ISO[A + Unit, (A, A)] with Comonoid[A] with Monoid[A] {
  override def fw(x: (A + Unit)): (A, A) = {
     x match {
       case Left(a) => split(a)
       case Right(u) => split(z)
     }
  }

  override def bw(y: (A, A)): (A + Unit) = {
     Left(reduce(y._1, y._2))
  }

  override def split(x: A): (A, A) = fw(Left(x))

  override def reduce(x: A, y: A): A = bw(x, y) match {
    case Left(a) => a
    case Right(_) => ???
  }

  override val z: A = { val p = fw(Right(())); reduce(p._1, p._2) }
}

trait Monad[F[_], A] {
  def join(xs: F[F[A]]): F[A]
  def unit(x: A): F[A]
}

trait Comonad[F[_], A] {
  def duplicate(xs: F[A]): F[F[A]]
  def counit(x: F[A]): A
}


trait GoldenF[F[_]] {

  def unit[A](x: Id[A]): F[A] = {
    val ys: F[F[A]] = fw(Right(x))
    bw(ys) match {
      case Left(n) => n
      case Right(zero) => bw(fw(Left(ys))) match {
        case Left(two) => ???
        case Right(one) => one
      }
    }
  }

  def flatten[A](xs: F[F[A]]): F[A] = extract(xs)

  def extract[A](xs: F[A]): Id[A] = {
    val ys: F[F[A]] = fw(Left(xs))
    bw(ys) match {
      case Left(zs) => extract(zs)
      case Right(z) => z
    }
  }

  def duplicate[A](xs: F[A]): F[F[A]] = unit(xs)

  def fw[A](x: F[A] + Id[A]): F[F[A]] = x match {
    case Left(xs) => unit(xs)
    case Right(x) => unit(unit(x))
  }

  def bw[A](ys: F[F[A]]): F[A] + Id[A] = {
    val xs: F[A] = extract(ys)
    val x: A = extract(xs)
    val zs = unit(x)
    if (zs == xs) Right(x) else Left(xs)
  }
}

case class GoldenList() extends GoldenF[List] {
  override def fw[A](x: +[List[A], A]): List[List[A]] = {
    x match {
      case Left(xs) => List(xs)
      case Right(x) => List(List(x))
    }
  }

  override def bw[A](ys: List[List[A]]): +[List[A], A] = {
    val xs: List[A] = ys.flatMap((x)=>x)
    if (xs.length == 1) Right(xs.head) else Left(xs)
  }
}

trait Stream[A] {
  def now: A
  def later: Stream[A]
  def extract: A = now
  def duplicate: Stream[Stream[A]] = futures
  def futures: Stream[Stream[A]] = {
    val self = this
    new Stream[Stream[A]] {
      def now = self
      override def later = self.later.futures
    }
  }

  def map[B](f: A=>B): Stream[B] =
  {
    val self = this
    new Stream[B] {
      override def now = f(self.now)
      override def later = self.later.map(f)
    }
  }

  def flatMap[B](f: A=>Stream[B]): Stream[B] =
  {
    val self = this
    def d(x: A): B = f(x).now
    def h = d(self.now)
    def t = self.later.map(d)
    new Stream[B] {
      override def now = h
      override def later = t
    }
  }

  def take(n0: Int): List[A] = {
    var n = n0
    val lb = new scala.collection.mutable.ListBuffer[A]
    var s = this
    while (n > 0) {
      lb += s.now
      s = s.later
      n = n - 1
    }
    lb.toList
  }

  def fold[B](z: B, f: (B, A)=> B): Stream[B] = {
    val self = this
    new Stream[B] {
      override def now = f(z, self.now)
      override def later = self.later.fold(now, f)
    }
  }

  def reduce(m: Monoid[A]): Stream[A] = fold(m.z, (x, y) => m.reduce(x, y))

  def zip[B, C](xs: Stream[B], f: (A, B)=>C): Stream[C] = {
    val self = this
    new Stream[C] {
      def now = f(self.now, xs.now)
      def later = self.later.zip(xs.later, f)
    }
  }

  override def toString: String = take(10).toString

  def followedBy(xs: Stream[A]): Stream[A] = {
    val self = this
    new Stream[A] {
      def now = self.now
      def later = xs
    }
  }
}


case class GoldenStream() extends GoldenF[Stream] {
  override def fw[A](e: Stream[A] + A): Stream[Stream[A]] = {
    e match {
      case Left(xs) => xs.duplicate
      case Right(x) => repeat(x).duplicate
    }
  }

  override def bw[A](ys: Stream[Stream[A]]): Stream[A] + A = {
    Left(ys.flatMap((x)=>x))
  }
}



object Lenses {

  type Id[A] = A
  type *[A, B] = (A, B)
  type /[A, B] = Lens[A, B]

  // A / A = 1
  def one[A]: (A / A) = One[A]

  // 1 / A
  def just[A] = new (A / Unit) {
    // project Unit from A
    override def get(x: A): Unit = ()
    // replace nothing in x with nothing
    override def set(x: A, nothing: Unit): A = x
  }

  // A / (A * B) = 1 / B
  def former[A, B]: (A, B) / A  = new ((A, B) / A) {
    def get(xs: (A, B)): A = xs._1
    def set(xs: (A, B), y: A): (A, B) = (y, xs._2)
  }

  // B / (A * B) = 1 / A
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

  def repeat[A](x: A): Stream[A] = new Stream[A] {
    def now = x
    def later = this
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
    list
  }

  def list: Unit = {
    val g = GoldenList()
    val l = g.unit(100)
    println(l)
    println(g.extract(l))

    val gs = GoldenStream()
    val xs: Stream[Int] = repeat(1)
    val m: Monoid[Int] =  new Monoid[Int] {
      override def z = 0
      override def reduce(x: Int, y: Int): Int = x + y
    }
    val sum = xs.reduce(m)
    println(sum.take(10))
    println(xs.take(10))
    val ys = gs.duplicate(xs)
    println(ys.take(10))

    def fib: Stream[Int] = repeat(0).followedBy(repeat(1)).zip(fib, (x: Int, y: Int) => x+y)
    println(fib.take(10))


  }
}
