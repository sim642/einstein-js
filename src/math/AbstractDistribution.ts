import {Distribution} from "./Distribution";
import {NumericPairs} from "./PairsDistribution";

export abstract class AbstractDistribution<T> implements Distribution<T> {
    abstract get(value: T): number | undefined;

    abstract n: number;
    abstract classes: number;

    abstract mapFreqs(f: (freq: number, value: T) => number): Distribution<T>;
    abstract map<U>(f: (freq: number, value: T) => U): U[];
    abstract filter(p: (freq: number, value: T) => boolean): Distribution<T>;

    scale(targetN: number): Distribution<T> {
        let sourceN = this.n;
        return this.mapFreqs(freq => freq / sourceN * targetN);
    }

    scaleTo<U>(targetDist: Distribution<U>): Distribution<T> {
        return this.scale(targetDist.n);
    }

    protected toPairs(): NumericPairs<T> {
        return this.map((freq, value) => [value, freq]) as NumericPairs<T>;
    }

    random(): T {
        // https://en.wikipedia.org/wiki/Fitness_proportionate_selection
        // http://www.keithschwarz.com/darts-dice-coins/ - Roulette Wheel Selection (linear)
        let pairs = this.toPairs();
        let cumFreq = Math.random() * this.n;
        for (let i = 0; i < pairs.length; i++) {
            let [value, freq] = pairs[i];
            if (cumFreq < freq) // value has range [0, freq)
                return value;
            else
                cumFreq -= freq;
        }
        return pairs[pairs.length - 1][0]; // must return in case of bad rounding

    }
}