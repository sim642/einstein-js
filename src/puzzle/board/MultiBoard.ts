import * as _ from 'lodash';
import {Board} from './Board';

type Variants = boolean[];

export class MultiBoard extends Board<Variants> {
    static fill(): MultiBoard {
        return new MultiBoard(_.times(Board.rows, _.constant(_.times(Board.cols, _.constant(_.times(Board.cols, _.constant(true)))))));
    }
}