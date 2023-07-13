<style>
    .pi-predicate {
        position: absolute;
    }

    .pi-predicate.dragged, .pi-predicate.dragged:hover, .pi-predicate.dragged:active {
        color: #fff!important;
        background-color: #007bff!important;
        border-color: #007bff!important;
    }

    .pi-predicate:hover, .pi-predicate:active {
        background-color:rgba(0, 0, 0, 0)!important;
        border-color:rgb(0, 123, 255)!important;
        color: rgb(0, 123, 255)!important;
        cursor: pointer;
    }
</style>

<template>
    <div class="btn btn-outline-primary pi-btn pi-predicate loading" :class="{'in-work-zone' : isInWorkZone(), 'in-hypothesis-zone' : !isInWorkZone() }" :data-handle="predicate.handle" draggable="true" v-html="html" @mousedown="mousedown" @mouseup="mouseup" @dragstart="dragStart" @dragend="dragEnd" @touchstart="touchstart" @touchend="touchend" v-touch:tap="tap" :id="uniqId()" @touchcancel="touchcancel"></div>
</template>

<script>
import _ from 'lodash';
import ButtonVue from './button.vue';

export default {
    extends: ButtonVue,
    props: [
        "predicate",
        "selectMode",
        "displayMode"
    ],
    computed: {
        alignment() {
            return "left";
        },
    },
    methods: {
        is: function(str) {
            return str == "predicate"; // Bad, allow to break polymorphism
        },

        toHTML: function() {
            return this.predicate.form.html();
        },

        toString: function() {
            return this.predicate.form.tostring();
        },

        toMathML: function() {
            return this.predicate.form.mathml();
        },

        setMetadata: function(metadata) {
            this.predicate.setmeta(metadata);
        },

        getMetadata: function() {
            return this.predicate.getmeta();
        },

        getSubGoal: function(e) {
            return this.predicate.parent;
        },

        getHandle: function(e) {
            return this.predicate.handle;
        },

        getRootId: function() {
            return this.getRootIdForType("H")
        },

        getPosition() {
            return this.predicate.position;
        },

        // override button.assignStaticPosition
        assignPosition() {
            if( this.hasSavedPosition() ) {
                this.restoreSavedPosition();
            }
            else {
                this.assignStaticPosition();
            }
        },

        dragStart: function(predicate, e) {
            // save the handle of the predicate into the event
            e.dataTransfer.setData("handle", predicate.handle);

            // also save the current mouse position relative to the predicate, so we can "correct" the position
            // at drop time (otherwise, it will align, at drop time, the top-left corner to the mouse position)
            var predicateDiv = $(`.pi-predicate[data-handle='${predicate.handle}']`);
            var offset = predicateDiv.offset();

            var deltaX = offset.left - e.clientX;
            var deltaY = offset.top  - e.clientY;
            e.dataTransfer.setData("deltaX", deltaX);
            e.dataTransfer.setData("deltaY", deltaY);
        },

        dragEnd: function() {
            this.$forceUpdate();
        },

        getCurrentZone: function() {
            if( this.isInWorkZone() ) {
                return "work-zone";
            }
            else {
                return "hypothesis-zone"
            }
        },

        quickSwitchToWorkZone: function() {
            var c = this.getCoord();
            this.setAbsolutePosition(c.x, c.y);
            $(this.$el).removeClass('in-hypothesis-zone').addClass('in-work-zone');
            var clone = $(this.$el).clone()
            clone.appendTo(this.$proofCanvas.getWorkZone());
            $(this.$el).remove();
            clone.mousedown();
        },
    }
}


</script>

