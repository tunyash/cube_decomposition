#include "bits/stdc++.h"

using namespace std;

class Mask {
   vector<int> _content;
public:
   Mask(const string& description) {
       _content.resize(description.size());
       for (size_t i = 0; i < description.size(); ++i) {
           switch (description[i]) {
               case '0': {
                   _content[i] = 0;
                   break;
               }
               case '1': {
                   _content[i] = 1;
                   break;
               }
               default: {
                   _content[i] = 2;
               }
           }
       }
   }

   Mask() {}

   Mask(size_t size, int base3encoding) {
       _content.resize(size);
       for (size_t i = 0; i < size; ++i) {
           _content[i] = base3encoding % 3;
           base3encoding /= 3;
       }
   }

   size_t size() const {
       return _content.size();
   }

   int getbit(size_t i) const {
       return _content[i];
   }

   Mask(const Mask& other) {
       _content = other._content;
   }
   bool within(const Mask &other) const {
       assert(other.size() == size());
       bool result = true;
       for (size_t i = 0; i < size(); ++i) {
           result &= getbit(i) == other.getbit(i) || other.getbit(i) == 2;
       }
       return result;
   }

   bool contains(const Mask& other) const {
       return other.within(*this);
   }

   bool intersects(const Mask& other) const {
       assert(other.size() == size());
       bool result = true;
       for (size_t i = 0; i < size(); ++i) {
           result &= getbit(i) + other.getbit(i) != 1;
       }
       return result;
   }

   bool disjoint(const Mask& other) const {
       return !intersects(other);
   }

   bool equals(const Mask& other) {
       return _content == other._content;
   }

   string tostring() const {
       string result = "";
       for (size_t i = 0; i < size(); ++i) {
           result.push_back(_content[i] == 2 ? '*': char('0' + _content[i]));
       }
       return result;
   }
};

bool is_hitting(vector<Mask>& masks) {
    int n = masks[0].size();
    vector<bool> covered(1<<n);
    int cov_count = 0;
    for (Mask mask : masks) {
        vector<int> stars;
        int base = 0;
        for (int i = 0; i < mask.size(); ++i) {
            if (mask.getbit(i) == 2) stars.push_back(1<<i);
            else if (mask.getbit(i) == 1) base |= 1 << i;
        }
        for (int j = 0; j < 1 << (stars.size()); ++j) {
            int r = base;
            for (size_t k = 0; k < stars.size(); ++k) {
                if ((j >> k) & 1) r |= stars[k];
            }
            if (covered[r]) {
                return false;
            }
            covered[r] = true;
            cov_count++;
        }
    }
    return cov_count == (1<< n);
}

bool is_irreducible(const vector<Mask>& masks, Mask& witness) {
    int n = masks[0].size();
    int three_to_n = 1;
    for (int i = 0; i < n; ++i) three_to_n *= 3;
    // -1 because we don't want *^n as a witness
    for (int mask_encoding = three_to_n - 2; mask_encoding >= 0; --mask_encoding) {
        Mask candidate(n, mask_encoding);
        bool result = true;
        // cout << "Candidate: " << candidate.tostring() << endl;
        for (Mask mask : masks) {
            // cout << "Mask: " << mask.tostring() << ' ' << mask.intersects(candidate) << ' ' << mask.within(candidate) << endl;
            if ((mask.intersects(candidate) && !mask.within(candidate) ) || (mask.equals(candidate))) {
                // cout << mask.tostring() << " kicks out " << candidate.tostring() << endl;
                result = false;                
                break;
            }
        }
        if (result) {
            witness = candidate;
            return false;
        }
    }
    return true;
}

vector<Mask> reduce(const vector<Mask>& masks) {
    cout << "Reducing: " << masks.size() << endl;
    Mask witness;
    if (is_irreducible(masks, witness)) return masks;
    vector<Mask> step;
    for (Mask mask : masks)
        if (!mask.within(witness)) step.push_back(mask);
    step.push_back(witness);
    return reduce(step);
}

int main() {
     int num_masks;
     cin >> num_masks;
     vector<Mask> masks;
     for (int i = 0; i < num_masks; ++i) {
         string s;
         cin >> s;
         masks.push_back(Mask(s));
     }
     cout << (is_hitting(masks) ? "Hitting" : "Not hitting") << endl;
     if (!is_hitting(masks)) return 0;
     Mask witness;
     bool result = is_irreducible(masks, witness);
     if (!result) {
         cout << "Reducible: " << witness.tostring() << endl;
         vector<Mask> reduced = reduce(masks);
         cout << reduced.size() << endl;
         for (Mask mask : reduced) cout << mask.tostring() << endl;
     } else {
         cout << "Irreducible" << endl;
     }
     
}