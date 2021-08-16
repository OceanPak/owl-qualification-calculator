import React from "react";

const RenderResultsRow = (props) =>{ // 3 tds here
    return props.keys.map((key, index)=>{
        return <td key={props.data[key]}>{props.data[key]}</td>
    })
}

class ResultsTable extends React.Component {

    getKeys = function(){
        var result = Object.keys(this.props.result[0]);
        result.push("2")
        return result
    }
      
    getRowsData = function(){
        var items = this.props.result;
        if (items.length <= 1) {
            return <div>
                <tr>
                    <th>Image</th>
                    <th>Team</th>
                    <th>Result</th>
                </tr>
            </div>
        }
        // var keys = this.getKeys();
        // console.log(keys)

        // https://stackoverflow.com/questions/19009591/how-to-break-a-line-or-space-in-between-two-rows-of-the-html-table/23897857
        return items.map((row, index)=>{ // 2 trs
            return <div>
                <tr>
                    <td>Image</td>
                    <td>{row[0].substring(0,3)}</td>
                    <td>{row[1][0]}</td>
                </tr>
                <tr>
                    <td>Image</td>
                    <td>{row[0].substring(4,7)}</td>
                    <td>{row[1][1]}</td>
                </tr>
                </div>
            // return <tr key={index}><RenderResultsRow key={index} data={row} keys={keys}/></tr>
        })
    }
      
    render() {
        return (
            <div>
                <table>
                    <tr>
                        <th>Match Result</th>
                    </tr>
                    <tbody>
                        {this.getRowsData()}
                    </tbody>
                </table>
            </div>
        );
    }
}

export default ResultsTable;
