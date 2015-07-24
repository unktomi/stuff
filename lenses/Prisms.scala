package lenses

/**
 * Created by christopheroliver on 10/18/14.
 */


import Prisms._


trait AbstractRaiser[T, A, B] {
  def raise(x: B): T
  def success(x: B): A
}

trait AbstractHandler[S, T, A] {
  def handle(y: S): A + T
}

// Parameter names are as in Kmett. S and T are "exceptions", A and B are "values". Evidently
// a more concrete prism will have to able to map B to A and S to T
trait AbstractPrism[S, T, A, B] extends AbstractRaiser[T, A, B] with AbstractHandler[S, T, A] {
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
/*
trait Either[A, B] {
  def cases[C](k1: A=>C, k2: B=>C): C
  def swap: Either[B, A] = {
    this match {
      case Left(x) => Right(x)
      case Right(y) => Left(y)
    }
  }
}

case class Left[A, B](val x: A) extends Either[A, B] {
  def cases[C](k1: A=>C, k2: B=>C): C = {
    k1(x)
  }
}

case class Right[A, B](val y: B) extends Either[A, B] {
  def cases[C](k1: A=>C, k2: B=>C): C = {
    k2(y)
  }
}
*/


// E ~= A + R
// E - A = R
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

}

// Evidence E is isomorphic to A + R
trait PrismISO[E, A, R] extends ISO[E, (A + R)] with (E - (A + R)) {
  override def raise(y: A + R): E = bw(y)
  override def handle(y: E): (A + R) + E = Left(fw(y))
}


// X + 1 - 2  = X - 1
case class MaybeNot[X](except: X) extends (Option[X] - Boolean) {

  override def raise(x: Boolean): Option[X] = if (x) Some(except) else None

  // inject A into E
  override def handle(y: Option[X]): Boolean + Option[X] = {
    y match {
      case Some(x) => if (y == except) Left(true) else Right(y)
      case None => Left(false)
    }
  }
}

// X - 1
case class Except[X](exception: X) extends (X - Unit) {
  // throw = dual of Lens.get
  override def raise(x: Unit): X = exception

  // inject A into E
  override def handle(y: X): Unit + X = y match {
    case exception => Left(())
    case _ => Right(y)
  }
}

// X - 2
case class Except2[X](yes: X, no: X) extends (X - Boolean) {
  // throw = dual of Lens.get
  override def raise(x: Boolean): X = x match {
    case false => no
    case true => yes
  }

  // inject A into E
  override def handle(y: X): Boolean + X = y match {
    case yes => Left(true)
    case no => Left(false)
    case _ => Right(y)
  }

}

// A - B
case class Subtype[A, B <: A]() extends (A - B) {
  // throw = dual of Lens.get
  override def raise(x: B): A = x

  // inject A into E
  override def handle(y: A): B + A = {
    if (y.isInstanceOf[B]) Left(y.asInstanceOf[B]) else Right(y)
  }
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

  def just1[A]: A - Nothing = new (A - Nothing) {
    // throw = dual of Lens.get
    override def raise(x: Nothing): A = x

    // inject A into E
    override def handle(y: A): Nothing + A = Right(y)
  }


  def laws[A, E](p: (E - A), v: A): Boolean = {
    val x: E = p.raise(v)
    println(v + " raise => "+x)
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
        case Left(ar) => ar match {
          case Left(a) => Left(a)
          case Right(r) => Right(y)
        }
        case Right(_) => Right(y)
      }
    }
  }

  // (A + E) - A = E
  def left[A, E]: (A + E) - A = prism(new PrismISO[A+E, A, E] {
    def fw(x: (A + E)): (A + E) = x
    def bw(y: (A + E)): (A + E) = y
  })

  // (A + E) - E = A
  def right[A, E]: (A + E) - E = prism(new PrismISO[A+E, E, A] {
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

  def minus1[X <: Exception] = new (Nothing - X) {
    // throw = dual of Lens.get
    override def raise(x: X): Nothing = throw x

    // inject A into E
    override def handle(y: Nothing): X + Nothing = Right(y)
  }

  def observer[X] = new (Unit - X) {
    var last: Option[X]  = None
    // throw = dual of Lens.get
    override def raise(x: X): Unit = {
       last = Some(x)
    }

    // inject A into E
    override def handle(y: Unit): X + Unit = {
       last match {
         case None => Right(())
         case Some(x) => Left(x)
       }
    }
  }


  def main(argv: Array[String]): Unit = {
    val p = left[Int, String]
    laws(p, 100)
    println(Lenses.laws(p.toLens, 100, Left(100)))
    println(p.toLens.get(100))
    println(p.toLens.set(200, Left(1000)))

    val notTen = MaybeNot[Int](10)
    println("Laws notTen: " + laws(notTen, true))
    println(notTen.raise(true))
    println(notTen.raise(false))
    println(notTen.handle(notTen.raise(true)))
    println(notTen.handle(None))
  }
}

