package main.scala.test.lenses

/**
 * Created by christopheroliver on 10/20/14.
 */
trait ISO[A, B] {
  def fw(x: A): B
  def bw(y: B): A
}