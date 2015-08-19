package lenses

/**
 * Created by christopheroliver on 7/25/15.
 */
// Isomorphism between A and B
trait ISO[A, B] {
  def fw(x: A): B
  def bw(y: B): A
}