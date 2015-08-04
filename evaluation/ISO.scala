package evaluation

/**
 * Created by coliver on 7/26/2015.
 */
// Isomorphism between A and B
trait ISO[A, B] {
  def fw(x: A): B
  def bw(y: B): A
}
