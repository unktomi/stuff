package lenses

/**
 * Created by christopheroliver on 10/23/14.
 */
sealed abstract class Exceptional[E, A] {

  def map[B](f: A=>B): Exceptional[E, B] = this match {
    case Fail(e) => Fail(e)
    case Success(x) => Success(f(x))
  }

  def flatMap[B](f: A => Exceptional[E, B]): Exceptional[E, B] = this match {
    case Fail(e) => Fail(e)
    case Success(x) => f(x)
  }

  def catchException (f: E => Exceptional[E, A]): Exceptional[E, A] = this match {
    case Fail(e) => f(e)
    case Success(x) => this
  }

  def extract: Either[E, A] = this match {
    case Fail(e) => Left(e)
    case Success(x) => Right(x)
  }
}

case class Fail[E, A](e: E) extends Exceptional[E, A]
case class Success[E, A](x: A) extends Exceptional[E, A]

object Exceptional {
  def raise[E, A](e: E): Exceptional[E, A] = Fail(e)
  def succeed[E, A](x: A): Exceptional[E, A] = Success(x)
  def handle[E, A](e: Either[E, A]): Exceptional[E, A] = {
     e match {
        case Left(e) => Fail(e)
        case Right(a) => Success(a)
     }
  }
}