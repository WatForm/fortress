package fortress.data;

import java.util.function.Function;
import java.lang.Iterable;
import java.util.stream.Stream;
import java.util.List;
import java.lang.UnsupportedOperationException;
import java.util.Collection;
import java.util.function.UnaryOperator;
import java.util.function.Function;
import java.util.Comparator;

// TODO need a more efficient way to build immutable lists
// e.g. ImmutableListBuilder class that you can only call getImmutable() on once.

public interface ImmutableList<E> extends List<E> {
    
    // Unsupported Operations
    
    @Override
    default public void add(int index, E element) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the add operation");
    }
    
    @Override
    default public boolean add(E value) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the add operation");
    }
    
    @Override
    default public boolean addAll(int index, Collection<? extends E> c) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the addAll operation");
    }
    
    @Override
    default public boolean addAll(Collection<? extends E> c) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the addAll operation");
    }
    
    @Override
    default public void clear() {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the clear operation");
    }
    
    @Override
    default public E remove(int index) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the remove operation");
    }
    
    @Override
    default public boolean remove(Object o) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the remove operation");
    }
    
    @Override
    default public void replaceAll(UnaryOperator<E> operator) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the replaceAll operation");
    }
    
    @Override
    default public boolean removeAll(Collection<?> c) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the removeAll operation");
    }
    
    @Override
    default public boolean retainAll(Collection<?> c) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the retainAll operation");
    }
    
    @Override
    default public E set(int index, E element) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the set operation");
    }
    
    @Override
    default public void sort(Comparator<? super E> c) {
        throw new UnsupportedOperationException("ImmutableList<E> does not support the sort operation");
    }
    
    // Overriden operations
    @Override
    public ImmutableList<E> subList(int fromIndex, int toIndex);
    
    // New operations
    public <R> ImmutableList<R> map(Function<? super E, ? extends R> mapping);
    
    // Static operations
    public static <T> ImmutableList<T> of(T item) {
        return new ImmutableWrapperList(List.of(item));
    }
}
