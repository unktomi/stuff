package main.scala.test.lenses

/**
 * Created by christopheroliver on 10/18/14.
 */

import java.io._

import Prisms._

 
// Parameter names are as in Kmett. S and T are "exceptions", A and B are "values". Evidently
// a more concrete prism will have to able to map B to A and S to T
trait AbstractPrism[S, T, A, B] {
  def raise(x: B): T
  def handle(y: S): A + T
  def success(x: B): A

  def doTry[X](f: X => B + S, xs: (X + S)): A + T = {
    xs match {
      // already an exception: handle it
      case Right(e) => handle(e)
      // try f
      case Left(a) => {
        val y: B + S = f(a)
        y match {
          // success: return it
          case Left(b) => Left(success(b))
          // catch e
          case Right(e) => handle(e)
        }
      }
    }
  }
  def tryCatch0[X](f: X => B): (X + S) => (A + T)  = (xs: (X + S)) => doTry((x: X)=>Left(f(x)), xs)
  def tryCatch[X](f: X => B + S): (X + S) => (A + T) = (xs: (X + S)) => doTry(f, xs)
}

// A ~= E + R
// E - A = -R
trait Prism[E, A] extends AbstractPrism[E, E, A, A] {
  type This = (E - A)
  // throw = dual of Lens.get
  def raise(x: A): E  // inject A into E
  // catch = dual of Lens.set
  def handle(y: E): (A + E) // analyze E into A or E

  override def success(x: A): A = x

  // def tryCatch[X](f: X => A + E): (X + E) => (A + E) = super.tryCatch(f)

  def +[F](xs: (F - E)) = compose(xs)
  // (E - A) + (F - E) = F - A
  def compose[F](you: F - E): F - A = {
    val me = this
    new Prism[F, A] {
      // throw
      override def raise(x: A): F = you.raise(me.raise(x))
      // catch
      override def handle(y: F): (A + F) = {
        you.handle(y) match {
          case Left(e) => me.handle(e) match {
            case Left(a) => Left(me.success(a))
            case Right(e) => Right(you.raise(e))
          }
          case Right(f) => Right(f)
        }
      }
    }
  }

  def swap: (A - E) = {
    val self = this
    new (A - E) {
      var store: Option[A] = None
      // throw = dual of Lens.get
      override def raise(x: E): A = store.get
      // E - (A - R) =  A
      override def handle(y: A): E + A = {
        store = Some(y)
        Right(y)
      }
    }
  }

  def toState: A=>(E, A) = {
    (x: A) => {
      (raise(x), x)
    }
  }

  def toLens: Lens[A, E] = {
    new Lens[A, E] {
      override def get(x: A): E = raise(x)
      override def set(x: A, y: E): A = handle(y) match {
        case Left(a) => a
        case Right(e) => x
      }
    }
  }

}

// A - A = 0
case class Zero[A]() extends (A - A) {
  // throw = id
  override def raise(x: A): A = x
  // catch = Left
  override def handle(y: A): (A + A) = Left(y)

  // -0
  override def swap(): Prism[A, A] = {
    val self = this
    new Prism[A, A] {
      // throw = id
      override def raise(x: A): A = x
      // catch = Right
      override def handle(y: A): (A + A) = Right(y)
      override def swap(): Prism[A, A] = self
    }
  }
}

// Evidence A is isomorphic to E + R
trait PrismISO[A, E, R] extends ISO[A, (E + R)] {
  def raise(y: E + R): A = bw(y)
  def handle(x: A): E + R = fw(x)
}

// X - 1 = X + 1 - 2
case class MaybeNot[X](except: X) extends (Option[X] - Boolean) {
  // throw = dual of Lens.get
  override def raise(x: Boolean): Option[X] = if (x) Some(except) else None

  // inject A into E
  override def handle(y: Option[X]): Boolean + Option[X] = {
    y match {
      case None => Left(false)
      case Some(v) => Right(y)
    }
  }
}

case class Never[X]() extends (Option[X] - Boolean) {

  override def raise(x: Boolean): Option[X] = None

  // inject A into E
  override def handle(y: Option[X]): Boolean + Option[X] = {
    Left(false)
  }
}

case class Throw[X](exception: X) extends (X - Unit) {
  // throw = dual of Lens.get
  override def raise(x: Unit): X = exception

  // inject A into E
  override def handle(y: X): Unit + X = if (y != exception) Left(()) else Right(y)

}

// File = File x InputStream + File x IOException
class FileISO extends PrismISO[File, (File, InputStream), (File, IOException)] {
  override def fw(x: File): +[(File, InputStream), (File, IOException)] = {
    try {
      Left((x, new FileInputStream(x)))
    } catch {
      case ex: IOException => Right((x, ex))
    }
  }

  override def bw(y: +[(File, InputStream), (File, IOException)]): File = {
    y match {
      case Left(xs) => xs._1
      case Right(xs) => xs._1
    }
  }
}

// File / File = (File x (InputStream + IOException)) / File
// Unit = InputStream + IOException
class OpenFile(x: File) extends PrismISO[Unit, InputStream, IOException] {
  override def fw(u: Unit): InputStream + IOException = {
    try {
      Left(new FileInputStream(x))
    } catch {
      case ex: IOException => Right(ex)
    }
  }
  override def bw(y: +[InputStream, IOException]): Unit = ()
}

object Prisms {

  implicit def rightToMaybe[X](xs: Unit + X): Option[X] = xs match {
    case Left(u) => None
    case Right(x) => Some(x)
  }

  implicit def leftToMaybe[X](xs: X + Unit): Option[X] = xs match {
    case Right(u) => None
    case Left(x) => Some(x)
  }

  implicit def optionToLeft[X](xs: Option[X]): (X + Unit) = xs match {
    case Some(x) => Left(x)
    case None => Right(())
  }

  type +[A, B] = Either[A, B]
  type -[A, E] = Prism[A, E]

  // A - A = 0
  def zero[A] = Zero[A]

  def just[A](x: A): (A + Unit) = Left(x)

  def nothing[A]: (A + Unit) = Right(())


  def laws[A, E](p: (E - A), v: A): Boolean = {
    val x: E = p.raise(v)
    p.handle(x) match {
      case Left(a) => println("Left "+a + " == " + v); a == v
      case Right(e) => println("Right "+ e + " == " + x); e == x
    }
  }
  // As in van Laarhoven
  def prism[A, E](iso: PrismISO[E, A, _]): (E - A) = {
    new (E - A) {
      override def raise(x: A): E = iso.raise(Left(x))
      override def handle(y: E): (A + E) = iso.handle(y) match {
        case Left(a) => Left(a)
        case Right(_) => Right(y)
      }
    }
  }

  // A - (A + E) = -E
  def left[A, E]: A+E - A = prism(new PrismISO[A+E, A, E] {
    def fw(x: (A + E)): (A + E) = x
    def bw(y: (A + E)): (A + E) = y
  })

  // E - (A + E) = A
  def right[A, E]: A+E - E = prism(new PrismISO[A+E, E, A] {
    def fw(x: (A + E)): (E + A) = x.swap
    def bw(y: (E + A)): (A + E) = y.swap
  })

  // as in Kmett
  def prism[A, E](remit: A=>E, review: E=>Option[A]): E - A = new (E - A) {
    // throw
    override def raise(x: A): E = remit(x)
    // catch
    override def handle(y: E): A + E = review(y) match {
      case None => Right(y)
      case Some(a) => Left(a)
    }
  }

  def main(argv: Array[String]): Unit = {
    val p = left[Int, String]
    laws(p, 100)
    println(Lenses.laws(p.toLens, 100, Left(100)))
    println(p.toLens.get(100))
    println(p.toLens.set(200, Left(1000)))

    val notTen = MaybeNot[Int](10)
    println("Laws notTen: " +laws(notTen, true))
    println(notTen.raise(true))
    println(notTen.raise(false))
    println(notTen.handle(notTen.raise(true)))
    println(notTen.handle(None))


    // X^2 + 2x + 1 = (x + 1) * (x + 1)
    def doit[X](xs: (X, X) + (X + X) + Unit): (X + Unit, X + Unit) = {
      xs match {
        case Left(p) => p match {
          case Left(xs) => (Left(xs._1), Left(xs._2))
          case Right(xx) => xx match {
            case Left(x1) => (Left(x1), Right(()))
            case Right(x2) => (Right(()), Left(x2))
          }
        }
        case Right(u) => (Right(()), (Right(())))
      }
    }

    // (X - 1) * (X - 1) = X2 -2x + 1 = x (x - 2) + 1  =
    def doit2[X](xs: (X, X - Boolean) + Unit): (Option[X] - Boolean, Option[X] - Boolean) = {
      xs match {
        case Left(xs) => val y: Boolean + X  = xs._2.handle(xs._1); y match {
          case Left(b) =>  val x = xs._2.raise(b); if (b) (MaybeNot(x), Never[X]) else (Never[X], MaybeNot(x))
          case Right(x) => (MaybeNot(x), MaybeNot(x))
        }
        //case Left(e) => e.(MaybeNot[X], MaybeNot[X])
        case Right(u) => (Never[X], Never[X])
      }
    }
  } 
}

