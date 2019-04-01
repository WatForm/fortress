package fortress.data;

import java.util.List;
import java.lang.Iterable;
import java.util.Iterator;
import java.util.ArrayList;
import fortress.util.Errors;
import java.lang.UnsupportedOperationException;

public class CartesianProduct<E> implements Iterable<List<E>> {
    
    private List<List<E>> sets;
    private int numberOfSets;
    private int[] numberOfElements;
    
    // Give a list A_1, ... A_n, where each is a list of elements
    public CartesianProduct(List<List<E>> sets) {
        this.sets = sets;
        this.numberOfSets = sets.size();
        for(List<E> set : sets) {
            Errors.precondition(set.size() > 0);
        }
    }
    
    @Override
    public Iterator iterator() {
        return new ProductIterator();
    }
    
    private class ProductIterator implements Iterator<List<E>> {
        private int[] currentPosition;
        private boolean atEnd;
        
        private ProductIterator() {
            this.currentPosition = new int[numberOfSets];
            this.atEnd = false;
            for(int i = 0; i < currentPosition.length; i++) {
                this.currentPosition[i] = 0;
            }
            this.currentPosition[0] = 0;
        }
        
        @Override
        public boolean hasNext() {
            return atEnd == false;
        }
        
        @Override
        public List<E> next() {
            Errors.precondition(hasNext());
            
            // Get current item of counter first
            List<E> productElement = new ArrayList<>();
            for(int i = 0; i < numberOfSets; i++) {
                List<E> set_i = sets.get(i);
                E element = set_i.get(currentPosition[i]);
                productElement.add(element);
            }
            
            // Increment
            int index = 0;
            while(index < numberOfSets && currentPosition[index] == sets.get(index).size() - 1) {
                currentPosition[index] = 0;
                index++;
            }
            if(index == numberOfSets) {
                atEnd = true;
            } else {
                currentPosition[index]++;
            }
            
            return productElement;
        }
        
        @Override
        public void remove() {
            throw new UnsupportedOperationException("remove is unsupported");
        }
    }
}
