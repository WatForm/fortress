package fortress.data;

import java.util.stream.Stream;
import java.util.Iterator;
import java.lang.Iterable;
import java.util.Collection;
import java.util.Set;
import cyclops.data.HashSet;
import cyclops.data.BankersQueue;

public class PersistentInsertionOrderedHashSet<E> implements PersistentSet<E> {
    private final HashSet<E> implSet;
    private final BankersQueue<E> queue;
    
    private PersistentInsertionOrderedHashSet(HashSet<E> implSet, BankersQueue<E> queue) {
        this.implSet = implSet;
        this.queue = queue;
    }
    
    // New operations
    public static PersistentInsertionOrderedHashSet empty() {
        return new PersistentInsertionOrderedHashSet(HashSet.empty(), BankersQueue.empty());
    }
    
    // PersistentSet operations
    @Override
    public PersistentSet<E> plus(E item) {
        if(containsValue(item)) {
            return this; // Have to worry about duplicates in queue
        }
        return new PersistentInsertionOrderedHashSet(implSet.plus(item), queue.plus(item));
    }
    
    public PersistentSet<E> plusAll(Iterable<? extends E> iterable) {
        // Have to worry about duplicates in queue, call plus which handles it
        PersistentSet<E> set = this;
        for(E item : iterable) {
            set = set.plus(item);
        }
        return set;
    }
    
    @Override
    public boolean containsValue(E value) {
        return implSet.containsValue(value);
    }
    
    // Set operations
    
    // TODO inefficient
    @Override
    public boolean contains(Object o) {
        for(E item : implSet) {
            if(item.equals(o)) {
                return true;
            }
        }
        return false;
    }
    
    // TODO inefficient
    @Override
    public boolean containsAll(Collection<?> c) {
        for(Object item : c) {
            if(!contains(item)) {
                return false;
            }
        }
        return true;
    }
    
    @Override
    public boolean equals(Object o) {
        return (o instanceof Set)
                && ((Set) o).size() == size()
                && containsAll((Set) o);
    }
    
    @Override
    public int hashCode() {
        return implSet.hashCode();
    }
    
    @Override
    public boolean isEmpty() {
        return implSet.isEmpty();
    }
    
    @Override
    public Iterator<E> iterator() {
        return queue.iterator();
    }
    
    @Override
    public int size() {
        return implSet.size();
    }
    
    @Override
    public Stream<E> stream() {
        return queue.stream();
    }
    
    @Override
    public Object[] toArray() {
        return queue.toArray();
    }
    
    // TODO must implement
    @Override
    public <T> T[] toArray(T[] as) {
        throw new UnsupportedOperationException("PersistentInsertionOrderedHashSet<E> does not support <T> T[] toArray(T[] a) at this time. It will be implemented.");
    } 
    
    @Override
    public String toString() {
        return implSet.toString();
    }
}
