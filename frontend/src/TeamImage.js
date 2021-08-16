import React, { Component } from "react";

import charge from './teamImages/charge.png'
import defiant from './teamImages/defiant.png'
import dragons from './teamImages/dragons.png'
import dynasty from './teamImages/dynasty.png'
import eternal from './teamImages/eternal.png'
import excelsior from './teamImages/excelsior.png'
import fuel from './teamImages/fuel.png'
import fusion from './teamImages/fusion.png'
import gladiators from './teamImages/gladiators.png'
import hunters from './teamImages/hunters.png'
import justice from './teamImages/justice.png'
import mayhem from './teamImages/mayhem.png'
import outlaws from './teamImages/outlaws.png'
import reign from './teamImages/reign.png'
import shock from './teamImages/shock.png'
import spark from './teamImages/spark.png'
import spitfire from './teamImages/spitfire.png'
import titans from './teamImages/titans.png'
import uprising from './teamImages/uprising.png'
import valiant from './teamImages/valiant.png'

class TeamImage extends Component { 
    constructor(props) {
        super(props);
    }

    render() {
        let image;

        if (this.props.team === "GZC") { image = charge }
        else if (this.props.team === "TOR") { image = defiant }
        else if (this.props.team === "SHD") { image = dragons }
        else if (this.props.team === "SEO") { image = dynasty }
        else if (this.props.team === "PAR") { image = eternal }
        else if (this.props.team === "NYE") { image = excelsior }
        else if (this.props.team === "DAL") { image = fuel }
        else if (this.props.team === "PHI") { image = fusion }
        else if (this.props.team === "GLA") { image = gladiators }
        else if (this.props.team === "CDH") { image = hunters }
        else if (this.props.team === "WAS") { image = justice }
        else if (this.props.team === "FLA") { image = mayhem }
        else if (this.props.team === "HOU") { image = outlaws }
        else if (this.props.team === "ATL") { image = reign }
        else if (this.props.team === "SFS") { image = shock }
        else if (this.props.team === "HZS") { image = spark }
        else if (this.props.team === "LDN") { image = spitfire }
        else if (this.props.team === "VAN") { image = titans }
        else if (this.props.team === "BOS") { image = uprising }
        else if (this.props.team === "VAL") { image = valiant }

        return (
            <img className={this.props.team} src={image} style={{height:"30px"}}/>
        );
      }
}

export default TeamImage;