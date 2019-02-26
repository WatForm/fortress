package fortress.data;

import java.util.Optional;
import java.util.function.Function;
import java.util.function.Consumer;
import java.lang.UnsupportedOperationException;

public class Either<L, R> {
    final Optional<L> left;
    final Optional<R> right;
    
    // Invariant: Exactly one of left or right is nonempty
    
    private Either(Optional<L> left, Optional<R> right) {
        this.left = left;
        this.right = right;
    }
    
    public static <L, R> Either<L, R> leftOf(L left) {
        return new Either(Optional.of(left), Optional.empty());
    }
    
    public static <L, R> Either<L, R> rightOf(R right) {
        return new Either(Optional.empty(), Optional.of(right));
    }
    
    public <T> T match(Function<L, T> ifLeft,
                       Function<R, T> ifRight) {
        if(left.isPresent()) {
            return ifLeft.apply(left.get());
        } else {
            return ifRight.apply(right.get());
        }
    }
    
    public void matchDo(Consumer<L> ifLeft,
                       Consumer<R> ifRight) {
        if(left.isPresent()) {
            ifLeft.accept(left.get());
        } else {
            ifRight.accept(right.get());
        }
    }
    
    public boolean isLeft() {
        return left.isPresent();
    }
    
    public boolean isRight() {
        return right.isPresent();
    }
    
    public L getLeft() {
        return left.get();
    }
    
    public R getRight() {
        return right.get();
    }
    
    
    // TODO implement these
    
    public boolean equals(Object o) {
        throw new UnsupportedOperationException("Either<L, R> does not support equals at this time. It will be implemented.");
    }
    
    public int hashCode() {
        throw new UnsupportedOperationException("Either<L, R> does not support hashCode at this time. It will be implemented.");
    }
}
